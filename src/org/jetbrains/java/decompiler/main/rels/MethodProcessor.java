// Copyright 2000_2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.main.rels;

import org.jetbrains.java.decompiler.api.java.JavaPassLocation;
import org.jetbrains.java.decompiler.api.plugin.LanguageSpec;
import org.jetbrains.java.decompiler.api.plugin.pass.PassContext;
import org.jetbrains.java.decompiler.code.CodeConstants;
import org.jetbrains.java.decompiler.code.Instruction;
import org.jetbrains.java.decompiler.code.InstructionSequence;
import org.jetbrains.java.decompiler.code.cfg.BasicBlock;
import org.jetbrains.java.decompiler.code.cfg.ControlFlowGraph;
import org.jetbrains.java.decompiler.code.cfg.ExceptionRangeCFG;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.collectors.CounterContainer;
import org.jetbrains.java.decompiler.main.decompiler.CancelationManager;
import org.jetbrains.java.decompiler.main.extern.IFernflowerLogger;
import org.jetbrains.java.decompiler.main.extern.IFernflowerPreferences;
import org.jetbrains.java.decompiler.main.plugins.PluginContext;
import org.jetbrains.java.decompiler.modules.code.DeadCodeHelper;
import org.jetbrains.java.decompiler.modules.decompiler.*;
import org.jetbrains.java.decompiler.modules.decompiler.decompose.DomHelper;
import org.jetbrains.java.decompiler.modules.decompiler.deobfuscator.ExceptionDeobfuscator;
import org.jetbrains.java.decompiler.modules.decompiler.flow.DirectGraph;
import org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper;
import org.jetbrains.java.decompiler.modules.decompiler.exps.*;
import org.jetbrains.java.decompiler.modules.decompiler.stats.*;
import org.jetbrains.java.decompiler.modules.decompiler.vars.VarProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.vars.VarTypeProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair;
import org.jetbrains.java.decompiler.struct.StructClass;
import org.jetbrains.java.decompiler.struct.StructMethod;
import org.jetbrains.java.decompiler.struct.gen.MethodDescriptor;
import org.jetbrains.java.decompiler.struct.gen.CodeType;
import org.jetbrains.java.decompiler.struct.gen.VarType;
import org.jetbrains.java.decompiler.util.DotExporter;
import org.jetbrains.java.decompiler.util.StartEndPair;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class MethodProcessor implements Runnable {
  public static ThreadLocal<RootStatement> debugCurrentlyDecompiling = ThreadLocal.withInitial(() -> null);
  public static ThreadLocal<ControlFlowGraph> debugCurrentCFG = ThreadLocal.withInitial(() -> null);
  public static ThreadLocal<DecompileRecord> debugCurrentDecompileRecord = ThreadLocal.withInitial(() -> null);
  public final Object lock = new Object();

  private final StructClass klass;
  private final StructMethod method;
  private final MethodDescriptor methodDescriptor;
  private final VarProcessor varProc;
  private final LanguageSpec spec;
  private final DecompilerContext parentContext;

  private volatile RootStatement root;
  private volatile Throwable error;
  private volatile boolean finished = false;

  public MethodProcessor(StructClass klass,
                         StructMethod method,
                         MethodDescriptor methodDescriptor,
                         VarProcessor varProc,
                         LanguageSpec spec,
                         DecompilerContext parentContext) {
    this.klass = klass;
    this.method = method;
    this.methodDescriptor = methodDescriptor;
    this.varProc = varProc;
    this.spec = spec;
    this.parentContext = parentContext;
  }

  @Override
  public void run() {
    error = null;
    root = null;

    try {
      DecompilerContext.setCurrentContext(parentContext);
      root = codeToJava(klass, method, methodDescriptor, varProc, spec);
    }
    catch (CancelationManager.CanceledException e) {
      throw e;
    }
    catch (Throwable t) {
      error = t;
    }
    finally {
      DecompilerContext.setCurrentContext(null);
    }

    finished = true;
    synchronized (lock) {
      lock.notifyAll();
    }
  }

  public static RootStatement codeToJava(StructClass cl, StructMethod mt, MethodDescriptor md, VarProcessor varProc, LanguageSpec spec) throws IOException {
    CancelationManager.checkCanceled();

    // Disable RTF for synthetic inner classes (switch-map $1/$2 classes).
    // RTF's IfHelper changes affect the main loop iteration count, which
    // changes StackVarsProcessor behavior on <clinit>, breaking switch-map
    // field resolution and producing <unrepresentable> in switch expressions.
    boolean rtfOverride = false;
    if (DecompilerContext.isRoundtripFidelity() && cl.qualifiedName.matches(".*\\$\\d+$")) {
      DecompilerContext.setProperty(IFernflowerPreferences.ROUNDTRIP_FIDELITY, "0");
      rtfOverride = true;
    }

    debugCurrentlyDecompiling.set(null);
    debugCurrentCFG.set(null);
    debugCurrentDecompileRecord.set(null);

    boolean isInitializer = CodeConstants.CLINIT_NAME.equals(mt.getName()); // for now static initializer only
    PluginContext pluginContext = PluginContext.getCurrentContext();

    mt.expandData(cl);
    InstructionSequence seq = mt.getInstructionSequence();
    ControlFlowGraph graph = new ControlFlowGraph(seq);
    debugCurrentCFG.set(graph);
    DotExporter.toDotFile(graph, mt, "cfgConstructed", true);

    DeadCodeHelper.removeDeadBlocks(graph);

    if (mt.getBytecodeVersion().hasJsr() || DecompilerContext.getOption(IFernflowerPreferences.FORCE_JSR_INLINE)) {
      graph.inlineJsr(cl, mt);
    }

    // TODO: move to the start, before jsr inlining
    DeadCodeHelper.connectDummyExitBlock(graph);

    DeadCodeHelper.removeGotos(graph);

    ExceptionDeobfuscator.removeCircularRanges(graph);

    ExceptionDeobfuscator.restorePopRanges(graph);

    if (DecompilerContext.getOption(IFernflowerPreferences.REMOVE_EMPTY_RANGES)) {
      ExceptionDeobfuscator.removeEmptyRanges(graph);
    }

    if (DecompilerContext.getOption(IFernflowerPreferences.ENSURE_SYNCHRONIZED_MONITOR)) {
      // special case: search for 'synchronized' ranges w/o monitorexit instruction (as generated by Kotlin and Scala)
      DeadCodeHelper.extendSynchronizedRangeToMonitorexit(graph);
    }

    if (DecompilerContext.getOption(IFernflowerPreferences.INCORPORATE_RETURNS)) {
      // special case: single return instruction outside of a protected range
      DeadCodeHelper.incorporateValueReturns(graph);
    }

    //		ExceptionDeobfuscator.restorePopRanges(graph);
    ExceptionDeobfuscator.insertEmptyExceptionHandlerBlocks(graph);

    DeadCodeHelper.mergeBasicBlocks(graph);

    DecompilerContext.getCounterContainer().setCounter(CounterContainer.VAR_COUNTER, mt.getLocalVariables());

    if (ExceptionDeobfuscator.hasObfuscatedExceptions(graph)) {
      DotExporter.toDotFile(graph, mt, "cfgExceptionsPre", true);

      if (!ExceptionDeobfuscator.handleMultipleEntryExceptionRanges(graph)) {
        DecompilerContext.getLogger().writeMessage("Found multiple entry exception ranges which could not be splitted", IFernflowerLogger.Severity.WARN);
        graph.addComment("$VF: Could not handle exception ranges with multiple entries");
        graph.addErrorComment = true;
      }

      DotExporter.toDotFile(graph, mt, "cfgMultipleExceptionEntry", true);
      ExceptionDeobfuscator.insertDummyExceptionHandlerBlocks(graph, mt.getBytecodeVersion());
      DotExporter.toDotFile(graph, mt, "cfgMultipleExceptionDummyHandlers", true);
    }

    if (spec != null) {
      DecompileRecord decompileRecord = new DecompileRecord(mt);

      RootStatement root = spec.graphParser.createStatement(graph, mt);

      PassContext pctx = new PassContext(root, graph, mt, cl, varProc, decompileRecord);
      spec.pass.run(pctx);

      if (rtfOverride) {
        DecompilerContext.setProperty(IFernflowerPreferences.ROUNDTRIP_FIDELITY, "1");
      }
      return root;
    }

    DotExporter.toDotFile(graph, mt, "cfgParsed", true);
    RootStatement root = DomHelper.parseGraph(graph, mt, 0);

    DecompileRecord decompileRecord = new DecompileRecord(mt);
    debugCurrentDecompileRecord.set(decompileRecord);

    decompileRecord.add("Initial", root);

    debugCurrentlyDecompiling.set(root);

    FinallyProcessor fProc = new FinallyProcessor(mt, md, varProc);
    int finallyProcessed = 0;

    while (fProc.iterateGraph(cl, mt, root, graph)) {
      finallyProcessed++;
      RootStatement oldRoot = root;
      decompileRecord.add("ProcessFinallyOld_" + finallyProcessed, root);
      DotExporter.toDotFile(graph, mt, "cfgProcessFinally_" + finallyProcessed, true);

      root = DomHelper.parseGraph(graph, mt, finallyProcessed);
      root.addComments(oldRoot);

      decompileRecord.add("ProcessFinally_" + finallyProcessed, root);

      debugCurrentCFG.set(graph);
      debugCurrentlyDecompiling.set(root);
    }

    // In rare cases, the final round of finally processing can reveal another synchronized statement. Try to parse it now.
    if (DomHelper.buildSynchronized(root)) {
      decompileRecord.add("BuildFinallySynchronized", root);
    }

    if (finallyProcessed > 0) {
      decompileRecord.add("ProcessFinally_Post", root);
    }

    // remove synchronized exception handler
    // not until now because of comparison between synchronized statements in the finally cycle
    if (DomHelper.removeSynchronizedHandler(root)) {
      decompileRecord.add("RemoveSynchronizedHandler", root);
    }

    root.buildContentFlags();

    //		LabelHelper.lowContinueLabels(root, new HashSet<StatEdge>());

    // SequenceHelper.condenseSequences(root);
    decompileRecord.add("CondenseSequences", root);

    ClearStructHelper.clearStatements(root);
    decompileRecord.add("ClearStatements", root);

    // Put exprents in statements
    ExprProcessor proc = new ExprProcessor(md, varProc);
    proc.processStatement(root, cl);
    decompileRecord.add("ProcessStatement", root);

    // SequenceHelper.condenseSequences(root);
    decompileRecord.add("CondenseSequences_1", root);

    // Process and simplify variables on the stack
    int stackVarsProcessed = 0;
    do {
      stackVarsProcessed++;

      StackVarsProcessor.simplifyStackVars(root, mt, cl);
      decompileRecord.add("SimplifyStackVars_PPMM_" + stackVarsProcessed, root);

      varProc.setVarVersions(root);
      decompileRecord.add("SetVarVersions_PPMM_" + stackVarsProcessed, root);
    } while (new PPandMMHelper(varProc).findPPandMM(root));

    // Reconstruct post-increment expressions (temp = var; ++var -> temp = var++)
    PPandMMHelper ppmmHelper = new PPandMMHelper(varProc);
    if (ppmmHelper.reconstructPostIncrement(root)) {
      decompileRecord.add("ReconstructPostIncrement", root);

      // Run another round of stack simplification to inline the post-increment assignments
      StackVarsProcessor.simplifyStackVars(root, mt, cl);
      decompileRecord.add("SimplifyStackVars_PostInc", root);

      varProc.setVarVersions(root);
      decompileRecord.add("SetVarVersions_PostInc", root);
    }

    PassContext pctx = new PassContext(root, graph, mt, cl, varProc, decompileRecord);

    // Inline ppi/mmi that we may have missed
    if (PPandMMHelper.inlinePPIandMMIIf(root)) {
      decompileRecord.add("InlinePPIandMMI", root);
    }

    // Process invokedynamic string concat
    if (cl.getVersion().hasIndyStringConcat()) {
      ConcatenationHelper.simplifyStringConcat(root);
      decompileRecord.add("SimplifyStringConcat", root);
    }

    // Plugin passes to run before the main decompilation loop
    pluginContext.runPasses(JavaPassLocation.BEFORE_MAIN, pctx);

    // Main loop
    while (true) {
      decompileRecord.incrementMainLoop();
      decompileRecord.add("Start", root);

      LabelHelper.cleanUpEdges(root);
      decompileRecord.add("CleanupEdges", root);

      if (root.hasLoops()) {
        // Merge loop
        while (true) {

          decompileRecord.incrementMergeLoop();
          decompileRecord.add("MergeLoopStart", root);

          if (EliminateLoopsHelper.eliminateLoops(root, cl)) {
            decompileRecord.add("EliminateLoops", root);
            continue;
          }

          MergeHelper.enhanceLoops(root);
          decompileRecord.add("EnhanceLoops", root);

          if (LoopExtractHelper.extractLoops(root)) {
            decompileRecord.add("ExtractLoops", root);
            continue;
          }

          // Plugin passes to run inside the merge loop
          if (pluginContext.runPasses(JavaPassLocation.IN_LOOP_DECOMP, pctx)) {
            continue;
          }

          if (IfHelper.mergeAllIfs(root)) {
            decompileRecord.add("MergeAllIfs", root);
            // Continues with merge loop
          } else {
            break;
          }
        }

        decompileRecord.resetMergeLoop();
        decompileRecord.add("MergeLoopEnd", root);
      }

      StackVarsProcessor.simplifyStackVars(root, mt, cl);
      decompileRecord.add("SimplifyStackVars", root);

      varProc.setVarVersions(root);
      decompileRecord.add("SetVarVersions", root);

      LabelHelper.identifyLabels(root);
      decompileRecord.add("IdentifyLabels", root);

      // Apply post processing transformations
      if (SecondaryFunctionsHelper.identifySecondaryFunctions(root, varProc)) {
        decompileRecord.add("IdentifySecondary", root);
        continue;
      }

      if (IntersectionCastProcessor.makeIntersectionCasts(root)) {
        decompileRecord.add("intersectionCasts", root);
        continue;
      }

      // RTF: skip pattern matching instanceof (e.g. `x instanceof Foo foo`) because
      // it generates a local variable for the cast result. The original bytecode uses
      // explicit casts like `((Foo)x).method()` which compiles to different bytecode
      // (ALOAD this vs ALOAD pattern_var).
      if (DecompilerContext.getOption(IFernflowerPreferences.PATTERN_MATCHING)
          && !DecompilerContext.isRoundtripFidelity()) {
        if (cl.getVersion().hasIfPatternMatching()) {
          if (IfPatternMatchProcessor.matchInstanceof(root)) {
            decompileRecord.add("MatchIfInstanceof", root);
            continue;
          }
        }
      }

      if (root.hasSwitch()) {
        boolean changed = false;
        if (SwitchPatternMatchProcessor.hasPatternMatch(root) && SwitchPatternMatchProcessor.processPatternMatching(root)) {
          decompileRecord.add("ProcessSwitchPatternMatch", root);
          changed = true;
        }

        if (SwitchExpressionHelper.hasSwitchExpressions(root) && SwitchExpressionHelper.processSwitchExpressions(root)) {
          decompileRecord.add("ProcessSwitchExpr", root);
          changed = true;
        }

        if (changed) {
          continue;
        }
      }

      if (root.hasTryCatch() && TryHelper.enhanceTryStats(root, cl)) {
        decompileRecord.add("EnhanceTry", root);
        continue;
      }

      // After try-with-resources reconstruction is complete (enhanceTryStats
      // returned false), inline temp return variables left over from JDK 9+
      // try-with-resources desugaring. The pattern:
      //   try (...) { ...; var = value; }  return var;
      // becomes:
      //   try (...) { ...; return value; }
      if (root.hasTryCatch() && TryHelper.inlineTwrReturnVars(root)) {
        // SequenceHelper.condenseSequences(root);
        decompileRecord.add("InlineTwrReturnVars", root);
        continue;
      }

      // RTF: inline temp return variables introduced by try-finally desugaring.
      // The pattern:
      //   Type var = default; try { ...; var = value; } finally { cleanup; } return var;
      // becomes:
      //   try { ...; return value; } finally { cleanup; }
      if (DecompilerContext.isRoundtripFidelity()
          && root.hasTryCatch()
          && TryHelper.inlineFinallyReturnVars(root)) {
        decompileRecord.add("InlineFinallyReturnVars", root);
        continue;
      }

      if (InlineSingleBlockHelper.inlineSingleBlocks(root)) {
        decompileRecord.add("InlineSingleBlocks", root);
        continue;
      }

      // this has to be done last so it does not screw up the formation of for loops
      if (root.hasLoops() && MergeHelper.makeDoWhileLoops(root)) {
        decompileRecord.add("MatchDoWhile", root);
        continue;
      }

      if (root.hasLoops() && MergeHelper.condenseInfiniteLoopsWithReturn(root)) {
        decompileRecord.add("CondenseDo", root);
        continue;
      }
  
      // Apply main loop plugin passes
      if (pluginContext.runPasses(JavaPassLocation.MAIN_LOOP, pctx)) {
        continue;
      }

      // initializer may have at most one return point, so no transformation of method exits permitted
      if (!isInitializer && ExitHelper.condenseExits(root)) {
        decompileRecord.add("CondenseExits", root);
        continue;
      }

      // FIXME: !!
      //if(EliminateLoopsHelper.eliminateLoops(root)) {
      //  continue;
      //}

      break;
    }
    decompileRecord.resetMainLoop();
    decompileRecord.add("MainLoopEnd", root);

    // RTF mode can leave unreachable statements after unconditional control
    // flow transfers (return/break/continue/throw) because condition negation
    // is blocked in IfHelper. Remove them so javac does not reject the output.
    // The DeadCodeEliminator skips switch case sequences and preserves
    // labeled blocks that are targets of break/continue from live code.
    // DeadCodeEliminator reduced label errors from 426 to 58 with the
    // isInLivePart fix, but still removes some label targets referenced
    // from live code. Needs further investigation into edge cases where
    // label edges are not detected by the current predecessor/label check.
    if (DecompilerContext.isRoundtripFidelity()) {
      if (DeadCodeEliminator.eliminateDeadCode(root)) {
        SequenceHelper.condenseSequences(root);
        decompileRecord.add("EliminateDeadCode", root);
      }
    }

    // this has to be done after all inlining is done so the case values do not get reverted
    if (root.hasSwitch() && SwitchHelper.simplifySwitches(root, mt, root)) {
      SequenceHelper.condenseSequences(root); // remove empty blocks
      decompileRecord.add("SimplifySwitches", root);

      // If we have simplified switches, try to make switch expressions
      if (SwitchExpressionHelper.hasSwitchExpressions(root)) {
        if (SwitchExpressionHelper.processSwitchExpressions(root)) {
          decompileRecord.add("ProcessSwitchExpr_SS", root);

          // Simplify stack vars to integrate and inline switch expressions
          StackVarsProcessor.simplifyStackVars(root, mt, cl);
          decompileRecord.add("SimplifyStackVars_SS", root);

          varProc.setVarVersions(root);
          decompileRecord.add("SetVarVersions_SS", root);
        }
      }
    }

    // Makes constant returns the same type as the method descriptor
    if (ExitHelper.adjustReturnType(root, md)) {
      decompileRecord.add("AdjustReturnType", root);
    }

    // Remove returns that don't need to exist
    if (ExitHelper.removeRedundantReturns(root)) {
      decompileRecord.add("RedundantReturns", root);
    }

    // Apply post processing transformations
    if (SecondaryFunctionsHelper.identifySecondaryFunctions(root, varProc)) {
      decompileRecord.add("IdentifySecondary", root);
    }

    // Improve synchronized monitor assignments
    if (SynchronizedHelper.cleanSynchronizedVar(root)) {
      decompileRecord.add("ClearSynchronized", root);
    }

    if (SynchronizedHelper.insertSink(root, varProc, root)) {
      decompileRecord.add("InsertSynchronizedAssignments", root);
    }

    // Apply plugin passes before setting variable definitions
    pluginContext.runPasses(JavaPassLocation.AFTER_MAIN, pctx);

    // RTF: narrow Object-typed variables to their actual usage type.
    // Type inference stabilizes with Object for erased generics because
    // getCommonSupertype(Object, X) = Object. This post-pass examines
    // how each Object variable is actually used and narrows the type.
    if (DecompilerContext.isRoundtripFidelity()) {
      VarTypeProcessor.narrowObjectTypes(root, varProc);
      // Upgrade raw collection types to generic based on lambda usage.
      VarTypeProcessor.upgradeRawCollectionTypes(root, varProc);
      // Mark all for-each loops to force var for their variables.
      // This must happen after narrowing so that for-each vars that were
      // narrowed from Object still get var (needed for raw collections).
      markForEachVar(root);
    }

    varProc.setVarDefinitions(root);
    decompileRecord.add("SetVarDefinitions", root);

    // Make sure to update assignments after setting the var definitions!
    if (SecondaryFunctionsHelper.updateAssignments(root)) {
      decompileRecord.add("UpdateAssignments", root);
    }

    // Hide empty default edges caused by switch statement processing
    if (root.hasSwitch() && LabelHelper.hideDefaultSwitchEdges(root)) {
      decompileRecord.add("HideEmptyDefault", root);
    }

    if (GenericsProcessor.qualifyChains(root)) {
      decompileRecord.add("QualifyGenericChains", root);
    }

    if (ExprProcessor.canonicalizeCasts(root)) {
      decompileRecord.add("CanonicalizeCasts", root);
    }

    // RTF: replace duplicate field reads in if-conditions with the variable
    // that was assigned from the same field in the head block. The original
    // bytecode used DUP to share a single field read; Vineflower splits this
    // into separate reads. This pass eliminates the redundant field access.
    if (DecompilerContext.isRoundtripFidelity()) {
      if (ExprProcessor.replaceDupFieldReadsInConditions(root)) {
        decompileRecord.add("ReplaceDupFieldReads", root);
      }
    }

    // Apply plugin passes after setting variable definitions
    pluginContext.runPasses(JavaPassLocation.AT_END, pctx);

    // must be the last invocation, because it makes the statement structure inconsistent
    // FIXME: new edge type needed
    if (LabelHelper.replaceContinueWithBreak(root)) {
      decompileRecord.add("ReplaceContinues", root);
    }

    // RTF: run dead code elimination again after replaceContinueWithBreak,
    // which can introduce continue statements that make subsequent code unreachable.
    if (DecompilerContext.isRoundtripFidelity()) {
      if (DeadCodeEliminator.eliminateDeadCode(root)) {
        SequenceHelper.condenseSequences(root);
        decompileRecord.add("EliminateDeadCode_Post", root);
      }
    }

    // RTF: hoist super()/this() out of label blocks in constructors.
    // Label blocks can wrap the entire constructor body including super(),
    // but Java requires super() to be the first statement.
    if (DecompilerContext.isRoundtripFidelity() && mt.getName().equals("<init>")) {
      hoistSuperFromLabelBlock(root);
    }

    // RTF: fix guard clause inversions by detecting IfStatements where the
    // condition direction was flipped from the original bytecode. For IFTYPE_IFELSE
    // statements, swap the if/else bodies and negate the condition to restore
    // the original branch direction.
    if (DecompilerContext.isRoundtripFidelity()) {
      fixGuardClauseInversions(root);
      fixGuardClauseLayout(root);
      fixLambdaOrdering(root);
      reInlineGuardClauses(root);
      extractMethodStartGuards(root, md);
      convertLoopExitReturnToBreak(root, md);
      restoreIincCompoundAssignments(root);
    }

    // RTF: final repair pass for orphaned label edges after all transformations.
    // Edges may have their closure set but not be registered in the closure's
    // labelEdges list, causing "break labelN;" to be emitted without a matching
    // label declaration.
    if (DecompilerContext.isRoundtripFidelity()) {
      LabelHelper.repairOrphanedLabels(root);
      LabelHelper.repairNullClosures(root);
    }

    // RTF: ensure non-void methods have return statements on all code paths.
    // In RTF mode, IfHelper transformations that would restructure if-else blocks
    // into proper return patterns are blocked (to preserve branch direction), which
    // can leave code paths without return statements.
    if (DecompilerContext.isRoundtripFidelity()) {
      if (ExitHelper.ensureMethodReturns(root, md)) {
        decompileRecord.add("EnsureMethodReturns", root);
      }
    }

    // RTF: re-introduce dead variable-to-variable stores that were eliminated
    // by SSA optimization. The original bytecode has these as load/store pairs,
    // and javac preserves them on recompilation.
    if (DecompilerContext.isRoundtripFidelity()) {
      if (reintroduceDeadStores(root, mt, varProc)) {
        decompileRecord.add("ReintroduceDeadStores", root);
      }
    }

    // Mark oddities in the decompiled code (left behind monitors, <unknown> variables, etc.)
    // No decompile record as statement structure is not modified
    ExprProcessor.markExprOddities(root);

    DotExporter.toDotFile(root, mt, "finalStatement");

    if (DotExporter.DUMP_DOTS) {
      FlattenStatementsHelper flatten = new FlattenStatementsHelper();
      DirectGraph digraph = flatten.buildDirectGraph(root);
      DotExporter.toDotFile(digraph, mt, "finalStatementDigraph");
    }

    // Debug print the decompile record
    DotExporter.toDotFile(decompileRecord, mt, "decompileRecord", false);

    mt.releaseResources();

    // Restore RTF if it was temporarily disabled for synthetic classes
    if (rtfOverride) {
      DecompilerContext.setProperty(IFernflowerPreferences.ROUNDTRIP_FIDELITY, "1");
    }

    return root;
  }

  /**
   * RTF: fix guard clause inversions by walking the statement tree bottom-up.
   * For IFTYPE_IFELSE with rtfConditionFlipped: swap if/else bodies and negate
   * condition. Works for all condition types (simple, compound, ternary) because
   * it operates on structure, not expression internals.
   * For IFTYPE_IF with rtfConditionFlipped: clear the flag without fixing
   * (known limitation with small per-method impact).
   */
  private static void fixGuardClauseInversions(Statement stat) {
    // Process children first (bottom-up) so inner if-statements are fixed
    // before outer ones that may depend on them.
    for (Statement child : new ArrayList<>(stat.getStats())) {
      fixGuardClauseInversions(child);
    }

    if (!(stat instanceof IfStatement)) {
      return;
    }
    IfStatement ifStat = (IfStatement) stat;
    if (!ifStat.isRtfConditionFlipped()) {
      return;
    }

    if (ifStat.iftype == IfStatement.IFTYPE_IFELSE) {
      Statement ifBody = ifStat.getIfstat();
      Statement elseBody = ifStat.getElsestat();
      if (ifBody != null && elseBody != null) {
        // Swap bodies
        ifStat.setIfstat(elseBody);
        ifStat.setElsestat(ifBody);
        ifStat.toggleRtfIfBodyIsFallThrough(); // bodies swapped

        // Swap edges
        StatEdge tmpEdge = ifStat.getIfEdge();
        ifStat.setIfEdge(ifStat.getElseEdge());
        ifStat.setElseEdge(tmpEdge);

        // Negate condition (double-negation cancels via propagateBoolNot)
        IfExprent headExpr = ifStat.getHeadexprent();
        Exprent negated = new FunctionExprent(
          FunctionExprent.FunctionType.BOOL_NOT, headExpr.getCondition(), null);
        Exprent simplified = SecondaryFunctionsHelper.propagateBoolNot(negated);
        headExpr.setCondition(simplified != null ? simplified : negated);
      }
    }
    // Note: IFTYPE_IF with null ifstat (goto-style) is NOT reversed here.
    // reorderIf's edge swap + condition negation for the noifstat path
    // preserves the correct javac opcode (double negation cancels).
    // Reversing would change the opcode and cause regressions.

    ifStat.setRtfConditionFlipped(false);
  }

  /**
   * RTF: fix block layout for guard clauses. javac places the if-body code first
   * (fall-through from condition) and the else-body after. When Vineflower puts
   * the main code as the if-body and a short return/throw as the else-body,
   * the compiled layout has the short block at the end - but the original had it
   * inline (before main code).
   *
   * Fix: for if-else where the else-body is a short terminating block (return/throw)
   * and the if-body is longer, swap them so javac places the short block first.
   */
  /**
   * RTF: add explicit return after CatchStatement when the catch body has a
   * preserved return but the try body's exit path has no explicit return.
   * Without this, javac adds a goto in the try body to skip the catch handler.
   */
  private static void addReturnAfterCatch(Statement stat, MethodDescriptor md) {
    if (md.ret.type != CodeType.VOID) return;

    for (Statement child : new ArrayList<>(stat.getStats())) {
      addReturnAfterCatch(child, md);
    }

    if (!(stat instanceof SequenceStatement)) return;
    SequenceStatement seq = (SequenceStatement) stat;

    // Only process CatchStatements that are the LAST statement in a root-level
    // sequence (at method end). Adding returns elsewhere adds unnecessary instructions.
    if (!(seq.getParent() instanceof RootStatement)) return;
    int lastIdx = seq.getStats().size() - 1;
    for (int i = lastIdx; i >= 0; i--) {
      Statement st = seq.getStats().get(i);
      if (!(st instanceof CatchStatement) && !(st instanceof CatchAllStatement)) continue;
      if (i != lastIdx) continue; // must be the last statement

      // Check if catch body ends with a void return
      List<Statement> children = st.getStats();
      if (children.size() < 2) continue;
      Statement catchBody = children.get(1);
      Statement lastInCatch = catchBody;
      while (!lastInCatch.getStats().isEmpty()) {
        lastInCatch = lastInCatch.getStats().get(lastInCatch.getStats().size() - 1);
      }
      if (lastInCatch.getExprents() == null || lastInCatch.getExprents().isEmpty()) continue;
      Exprent lastExpr = lastInCatch.getExprents().get(lastInCatch.getExprents().size() - 1);
      if (!(lastExpr instanceof ExitExprent)) continue;
      ExitExprent exit = (ExitExprent) lastExpr;
      if (exit.getExitType() != ExitExprent.Type.RETURN || exit.getValue() != null) continue;

      // Check next statement - is it already a return?
      Statement next = seq.getStats().get(i + 1);
      if (next instanceof BasicBlockStatement) {
        List<Exprent> nextExprents = next.getExprents();
        if (nextExprents != null && !nextExprents.isEmpty()) {
          Exprent nextLast = nextExprents.get(nextExprents.size() - 1);
          if (nextLast instanceof ExitExprent) continue; // already has return
        }
      }

      // Add explicit return; after the CatchStatement.
      // This ensures both try and catch paths have separate returns,
      // matching the original bytecode's 2-return pattern.
      BasicBlockStatement returnBlock = new BasicBlockStatement(
          new BasicBlock(
              DecompilerContext.getCounterContainer().getCounterAndIncrement(CounterContainer.STATEMENT_COUNTER)));
      List<Exprent> returnExprents = new ArrayList<>();
      returnExprents.add(new ExitExprent(ExitExprent.Type.RETURN, null, VarType.VARTYPE_VOID, null, null));
      returnBlock.setExprents(returnExprents);

      seq.getStats().addWithKeyAndIndex(i + 1, returnBlock, returnBlock.id);
      returnBlock.setParent(seq);
      break; // only add once per sequence
    }
  }

  private static void fixGuardClauseLayout(Statement stat) {
    for (Statement child : new ArrayList<>(stat.getStats())) {
      fixGuardClauseLayout(child);
    }

    if (!(stat instanceof IfStatement)) return;
    IfStatement ifStat = (IfStatement) stat;
    if (ifStat.iftype != IfStatement.IFTYPE_IFELSE) return;

    Statement ifBody = ifStat.getIfstat();
    Statement elseBody = ifStat.getElsestat();
    if (ifBody == null || elseBody == null) return;

    // javac places the if-body as fall-through (first in bytecode) and the
    // else-body after. To match the original layout, the if-body should
    // contain code from the LOWER bytecode offset (the original fall-through).
    // Compare the start offsets of the if-body and else-body to determine
    // which was the original fall-through.
    StartEndPair ifRange = ifBody.getStartEndRange();
    StartEndPair elseRange = elseBody.getStartEndRange();

    // If the else-body starts at a lower offset than the if-body,
    // the else was the original fall-through and should be the if-body.
    if (elseRange.start >= 0 && ifRange.start >= 0 && elseRange.start < ifRange.start) {
      swapIfElseBranches(ifStat);
    }
  }

  private static void swapIfElseBranches(IfStatement ifStat) {
    Statement ifBody = ifStat.getIfstat();
    Statement elseBody = ifStat.getElsestat();

    ifStat.setIfstat(elseBody);
    ifStat.setElsestat(ifBody);
    ifStat.toggleRtfIfBodyIsFallThrough(); // bodies swapped

    StatEdge tmpEdge = ifStat.getIfEdge();
    ifStat.setIfEdge(ifStat.getElseEdge());
    ifStat.setElseEdge(tmpEdge);

    IfExprent headExpr = ifStat.getHeadexprent();
    Exprent negated = new FunctionExprent(
      FunctionExprent.FunctionType.BOOL_NOT, headExpr.getCondition(), null);
    Exprent simplified = SecondaryFunctionsHelper.propagateBoolNot(negated);
    headExpr.setCondition(simplified != null ? simplified : negated);
  }

  /** Check if a statement is a simple terminating block (just return/throw with a constant or simple expression). */
  /**
   * RTF: re-inline guard clauses into if-else structures.
   *
   * The IfStatement constructor extracts guard clauses (return/throw) as the
   * ifstat, with the body code becoming a sibling in the parent SequenceStatement.
   * The rtfOriginalHadGotoFallthrough rendering trick then produces:
   *   if(!cond){} else{guard_clause};  body_code_sibling;
   *
   * This re-inlines by absorbing the body sibling into the IfStatement:
   *   if(cond){body_code} else{guard_clause}
   *
   * This produces the exact original bytecode: correct opcode, correct goto.
   * Pattern follows reorderIf() in IfHelper.java.
   */
  private static void reInlineGuardClauses(Statement stat) {
    for (Statement child : new ArrayList<>(stat.getStats())) {
      reInlineGuardClauses(child);
    }

    if (!(stat instanceof IfStatement)) return;
    IfStatement ifStat = (IfStatement) stat;

    if (ifStat.iftype != IfStatement.IFTYPE_IF) return;
    if (!ifStat.isRtfOriginalHadGotoFallthrough()) return;

    // ifstat is the guard clause (return/throw) - must be terminating
    Statement guardClause = ifStat.getIfstat();
    if (guardClause == null) return;
    if (guardClause.getExprents() == null || guardClause.getExprents().isEmpty()) return;
    Exprent lastExpr = guardClause.getExprents().get(guardClause.getExprents().size() - 1);
    if (!(lastExpr instanceof ExitExprent)) return;

    // Skip compound conditions - the rendering has special handling
    IfExprent headExpr = ifStat.getHeadexprent();
    if (headExpr != null) {
      Exprent cond = headExpr.getCondition();
      if (cond instanceof FunctionExprent) {
        FunctionExprent.FunctionType ft = ((FunctionExprent) cond).getFuncType();
        if (ft == FunctionExprent.FunctionType.BOOLEAN_AND || ft == FunctionExprent.FunctionType.BOOLEAN_OR) {
          return;
        }
      }
    }

    // Parent must be a SequenceStatement with a next sibling
    Statement parent = ifStat.getParent();
    if (!(parent instanceof SequenceStatement)) return;
    SequenceStatement parentSeq = (SequenceStatement) parent;

    int ifIndex = parentSeq.getStats().getIndexByKey(ifStat.id);
    if (ifIndex < 0 || ifIndex >= parentSeq.getStats().size() - 1) return;
    Statement bodySibling = parentSeq.getStats().get(ifIndex + 1);

    // Safety: immediate sibling must have exactly 1 regular predecessor
    List<StatEdge> sibPreds = bodySibling.getPredecessorEdges(StatEdge.TYPE_REGULAR);
    if (sibPreds.size() != 1) return;

    // Safety: IfStatement must have a successor edge
    List<StatEdge> ifSuccs = ifStat.getSuccessorEdges(Statement.STATEDGE_DIRECT_ALL);
    if (ifSuccs.isEmpty()) return;

    // === Transform: absorb ALL remaining siblings as if-body ===
    // Following the pattern from reorderIf() in IfHelper.java (lines 800-816):
    // collect all siblings after the IfStatement and wrap in a SequenceStatement
    // if there are multiple.

    List<Statement> bodyStatements = new ArrayList<>();
    for (int j = ifIndex + 1; j < parentSeq.getStats().size(); j++) {
      bodyStatements.add(parentSeq.getStats().get(j));
    }

    Statement bodyBlock;
    if (bodyStatements.size() == 1) {
      bodyBlock = bodyStatements.get(0);
    } else {
      bodyBlock = new SequenceStatement(bodyStatements);
      bodyBlock.setAllParent();
    }

    // 1. Remove IfStatement's successor edge
    ifStat.removeSuccessor(ifSuccs.get(0));

    // 2. Move the LAST body statement's successor edges to the IfStatement
    Statement lastBody = bodyStatements.get(bodyStatements.size() - 1);
    for (StatEdge edge : new ArrayList<>(lastBody.getAllSuccessorEdges())) {
      lastBody.removeSuccessor(edge);
      edge.setSource(ifStat);
      ifStat.addSuccessor(edge);
    }

    // 3. Remove all body siblings from parent
    for (Statement st : bodyStatements) {
      parentSeq.getStats().removeWithKey(st.id);
    }

    // 4. Old ifedge (first -> guardClause) becomes elseedge
    StatEdge oldIfEdge = ifStat.getIfEdge();

    // 5. New ifedge: first -> bodyBlock
    StatEdge newIfEdge = new StatEdge(StatEdge.TYPE_REGULAR, ifStat.getFirst(), bodyBlock);
    ifStat.getFirst().addSuccessor(newIfEdge);

    // 6. Wire up IFTYPE_IFELSE
    ifStat.setElsestat(guardClause);
    ifStat.setElseEdge(oldIfEdge);
    ifStat.setIfstat(bodyBlock);
    ifStat.setIfEdge(newIfEdge);

    ifStat.getStats().addWithKey(bodyBlock, bodyBlock.id);
    bodyBlock.setParent(ifStat);

    ifStat.iftype = IfStatement.IFTYPE_IFELSE;

    // 7. Negate condition - the condition was for the guard clause,
    //    now it needs to be for the body (opposite polarity)
    IfExprent condExpr = ifStat.getHeadexprent();
    Exprent negated = new FunctionExprent(
        FunctionExprent.FunctionType.BOOL_NOT, condExpr.getCondition(), null);
    Exprent simplified = SecondaryFunctionsHelper.propagateBoolNot(negated);
    condExpr.setCondition(simplified != null ? simplified : negated);

    // 8. Update RTF tracking
    ifStat.setNegated(!ifStat.isNegated());
    ifStat.toggleRtfIfBodyIsFallThrough();
    ifStat.toggleRtfConditionFlipped();
  }

  /**
   * RTF: extract guard clauses absorbed into method-level wrapping ifs.
   * Pattern: if (cond) { entire_body } at method level in a void method.
   * The original was: if (!cond) { return; } body
   * Convert IFTYPE_IF wrapping body -> IFTYPE_IF guard + sibling body.
   */
  private static void extractMethodStartGuards(Statement root, MethodDescriptor md) {
    if (md.ret.type != CodeType.VOID) return;

    // Find the IfStatement at method level
    Statement first = root.getFirst();
    IfStatement ifStat = null;

    if (first instanceof IfStatement) {
      ifStat = (IfStatement) first;
    } else if (first instanceof SequenceStatement) {
      SequenceStatement seq = (SequenceStatement) first;
      int lastIdx = seq.getStats().size() - 1;
      if (lastIdx >= 0 && seq.getStats().get(lastIdx) instanceof IfStatement) {
        ifStat = (IfStatement) seq.getStats().get(lastIdx);
      }
    }

    if (ifStat == null) return;
    if (ifStat.iftype != IfStatement.IFTYPE_IF) return;
    if (ifStat.getIfstat() == null) return;
    if (ifStat.getElsestat() != null) return;

    // Verify: head block had a guard clause pattern (ifXX + return)
    Statement head = ifStat.getFirst();
    if (!(head instanceof BasicBlockStatement)) return;
    BasicBlock headBlock = ((BasicBlockStatement) head).getBlock();
    if (!headBlock.rtfFallthroughWasReturn && !headBlock.rtfFallthroughWasGoto) return;

    // If-body is the extracted body
    Statement ifBody = ifStat.getIfstat();

    // If-body must be non-trivial
    if (ifBody instanceof BasicBlockStatement) {
      List<Exprent> exprents = ifBody.getExprents();
      if (exprents != null && exprents.size() <= 1) return;
    }

    // === Transform ===

    // Create guard return block
    BasicBlockStatement guardBlock = new BasicBlockStatement(
        new BasicBlock(
            DecompilerContext.getCounterContainer().getCounterAndIncrement(CounterContainer.STATEMENT_COUNTER)));
    guardBlock.setExprents(new ArrayList<>(List.of(
        new ExitExprent(ExitExprent.Type.RETURN, null, VarType.VARTYPE_VOID, null, null))));

    // Detach if-body from IfStatement
    ifStat.getStats().removeWithKey(ifBody.id);
    StatEdge oldIfEdge = ifStat.getIfEdge();
    if (oldIfEdge != null) {
      ifStat.getFirst().removeSuccessor(oldIfEdge);
    }

    // Set guard block as new if-body
    ifStat.setIfstat(guardBlock);
    ifStat.getStats().addWithKey(guardBlock, guardBlock.id);
    guardBlock.setParent(ifStat);
    StatEdge newIfEdge = new StatEdge(StatEdge.TYPE_REGULAR, ifStat.getFirst(), guardBlock);
    ifStat.getFirst().addSuccessor(newIfEdge);
    ifStat.setIfEdge(newIfEdge);

    // Negate condition
    IfExprent condExpr = ifStat.getHeadexprent();
    if (condExpr != null) {
      Exprent negated = new FunctionExprent(
          FunctionExprent.FunctionType.BOOL_NOT, condExpr.getCondition(), null);
      Exprent simplified = SecondaryFunctionsHelper.propagateBoolNot(negated);
      condExpr.setCondition(simplified != null ? simplified : negated);
    }

    // Move successor edges from ifStat to ifBody (the body now exits the method)
    for (StatEdge edge : new ArrayList<>(ifStat.getAllSuccessorEdges())) {
      ifStat.removeSuccessor(edge);
      edge.setSource(ifBody);
      ifBody.addSuccessor(edge);
    }

    // Create SequenceStatement: [guard-if, extracted-body]
    SequenceStatement wrapper = new SequenceStatement(Arrays.asList(ifStat, ifBody));
    ifStat.setParent(wrapper);
    ifBody.setParent(wrapper);

    // if -> body fall-through
    ifStat.addSuccessor(new StatEdge(StatEdge.TYPE_REGULAR, ifStat, ifBody));

    // Replace the old first child in root with the wrapper
    if (first == ifStat) {
      // IfStatement was direct child of root
      root.getStats().removeWithKey(ifStat.id);
      root.getStats().addWithKeyAndIndex(0, wrapper, wrapper.id);
      wrapper.setParent(root);
      root.setFirst(wrapper);
    } else if (first instanceof SequenceStatement) {
      // IfStatement was last child of a sequence
      SequenceStatement seq = (SequenceStatement) first;
      int idx = seq.getStats().getIndexByKey(ifStat.id);
      seq.getStats().removeWithKey(ifStat.id);
      // Add wrapper's children (ifStat and ifBody) as siblings
      seq.getStats().addWithKeyAndIndex(idx, ifStat, ifStat.id);
      ifStat.setParent(seq);
      seq.getStats().addWithKeyAndIndex(idx + 1, ifBody, ifBody.id);
      ifBody.setParent(seq);
    }
  }

  /**
   * RTF: convert loop-exit return to break + post-loop return.
   * Pattern: while(true) { ... if(cond){return;} ... }
   * becomes: while(true) { ... if(cond){break;} ... } return;
   *
   * This makes javac emit goto (break) + shared return, matching the
   * original bytecode which had goto + return instead of inline return.
   */
  private static void convertLoopExitReturnToBreak(Statement stat, MethodDescriptor md) {
    if (md.ret.type != CodeType.VOID) return;

    for (Statement child : new ArrayList<>(stat.getStats())) {
      convertLoopExitReturnToBreak(child, md);
    }

    if (!(stat instanceof DoStatement)) return;
    DoStatement loop = (DoStatement) stat;
    if (loop.getLooptype() != DoStatement.Type.INFINITE) return;

    // Find if-statements inside the loop body that have a void return as if-body
    Statement loopBody = loop.getFirst();
    List<Statement> bodyChildren = collectSequenceChildren(loopBody);

    for (Statement child : bodyChildren) {
      if (!(child instanceof IfStatement)) continue;
      IfStatement ifStat = (IfStatement) child;
      if (ifStat.iftype != IfStatement.IFTYPE_IF) continue;

      Statement ifBody = ifStat.getIfstat();
      if (ifBody == null) continue;
      if (!(ifBody instanceof BasicBlockStatement)) continue;

      List<Exprent> exprents = ifBody.getExprents();
      if (exprents == null || exprents.size() != 1) continue;
      if (!(exprents.get(0) instanceof ExitExprent)) continue;

      ExitExprent exit = (ExitExprent) exprents.get(0);
      if (exit.getExitType() != ExitExprent.Type.RETURN || exit.getValue() != null) continue;

      // Verify: the head block had rtfFallthroughWasGoto (the original had
      // goto to a shared return, not inline return)
      Statement head = ifStat.getFirst();
      if (!(head instanceof BasicBlockStatement)) continue;
      BasicBlock headBlock = ((BasicBlockStatement) head).getBlock();
      if (!headBlock.rtfFallthroughWasGoto) continue;

      // Convert: remove the return exprent, replace with break edge logic
      exprents.clear();

      // Remove old if-edge and add break edge to loop
      StatEdge oldIfEdge = ifStat.getIfEdge();
      if (oldIfEdge != null) {
        ifStat.getFirst().removeSuccessor(oldIfEdge);
      }

      // The if-body becomes a break target
      StatEdge breakEdge = new StatEdge(StatEdge.TYPE_BREAK, ifStat.getFirst(), loop.getParent(), loop);
      ifStat.getFirst().addSuccessor(breakEdge);
      ifStat.setIfEdge(breakEdge);
      ifStat.setIfstat(null);
      ifStat.getStats().removeWithKey(ifBody.id);

      // Add explicit return; after the loop in the parent sequence
      Statement loopParent = loop.getParent();
      if (loopParent instanceof SequenceStatement) {
        SequenceStatement parentSeq = (SequenceStatement) loopParent;
        int loopIdx = parentSeq.getStats().getIndexByKey(loop.id);
        if (loopIdx >= 0) {
          BasicBlockStatement returnBlock = new BasicBlockStatement(
              new BasicBlock(
                  DecompilerContext.getCounterContainer().getCounterAndIncrement(CounterContainer.STATEMENT_COUNTER)));
          returnBlock.setExprents(new ArrayList<>(List.of(
              new ExitExprent(ExitExprent.Type.RETURN, null, VarType.VARTYPE_VOID, null, null))));
          parentSeq.getStats().addWithKeyAndIndex(loopIdx + 1, returnBlock, returnBlock.id);
          returnBlock.setParent(parentSeq);
        }
      }

      break; // only handle first loop-exit guard per loop
    }
  }

  private static List<Statement> collectSequenceChildren(Statement stat) {
    if (stat instanceof SequenceStatement) {
      return new ArrayList<>(stat.getStats());
    }
    return List.of(stat);
  }

  /**
   * RTF: restore compound assignment form for iinc bytecode instructions.
   * During initial processing, iinc is decompiled as var = var + const.
   * SSA splitting changes the versions, making compound assignment detection
   * fail. The rtfIincType tag preserves the original operator so we can
   * restore var += const after all SSA processing is complete.
   */
  private static void restoreIincCompoundAssignments(Statement stat) {
    if (stat.getExprents() != null) {
      for (Exprent expr : stat.getExprents()) {
        restoreIincInExprent(expr);
      }
    }
    for (Statement child : stat.getStats()) {
      restoreIincCompoundAssignments(child);
    }
  }

  private static void restoreIincInExprent(Exprent expr) {
    if (expr instanceof AssignmentExprent) {
      AssignmentExprent assign = (AssignmentExprent) expr;
      if (assign.getRtfIincType() != null && assign.getCondType() == null) {
        // This was an iinc instruction. Convert to compound assignment.
        // The right side is currently: FunctionExprent(ADD/SUB, [var, const])
        // We need to extract the const and set it as the new right side.
        Exprent right = assign.getRight();
        if (right instanceof FunctionExprent) {
          FunctionExprent func = (FunctionExprent) right;
          if (func.getLstOperands().size() == 2) {
            // The const is the second operand (for ADD: var + const)
            // or first operand if commutative and swapped
            Exprent constOp = func.getLstOperands().get(1);
            if (constOp instanceof ConstExprent) {
              assign.setRight(constOp);
              assign.setCondType(assign.getRtfIincType());
            }
          }
        }
      }
    }
    // Recurse into sub-expressions
    for (Exprent child : expr.getAllExprents()) {
      restoreIincInExprent(child);
    }
  }

  private static boolean isSimpleTerminating(Statement stat) {
    // Direct basic block with return/throw
    if (stat.getExprents() != null) {
      if (stat.getExprents().size() == 1) {
        Exprent expr = stat.getExprents().get(0);
        if (expr instanceof ExitExprent) {
          // Simple return: return, return constant, return variable, return field
          ExitExprent exit = (ExitExprent) expr;
          if (exit.getValue() == null) return true; // void return
          if (exit.getValue() instanceof ConstExprent) return true; // return 0, return null
          if (exit.getValue() instanceof VarExprent) return true; // return var
          if (exit.getValue() instanceof FieldExprent) return true; // return field
          return false; // complex return expression
        }
      }
      return false;
    }
    // Sequence ending in simple termination
    if (stat.type == Statement.StatementType.SEQUENCE) {
      List<Statement> stats = stat.getStats();
      return !stats.isEmpty() && isSimpleTerminating(stats.get(stats.size() - 1));
    }
    return false;
  }

  /** Estimate the bytecode instruction count of a statement (rough). */
  private static int estimateInsnCount(Statement stat) {
    int count = 0;
    if (stat.getExprents() != null) {
      count = stat.getExprents().size(); // rough: 1 exprent ≈ 1-3 insns
    }
    for (Statement child : stat.getStats()) {
      count += estimateInsnCount(child);
    }
    return count;
  }

  /** Check if a statement always terminates (return or throw on all paths). */
  private static boolean isTerminating(Statement stat) {
    if (stat.getExprents() != null && !stat.getExprents().isEmpty()) {
      Exprent last = stat.getExprents().get(stat.getExprents().size() - 1);
      return last instanceof ExitExprent;
    }
    // Sequence: last child must terminate
    if (stat.type == Statement.StatementType.SEQUENCE) {
      List<Statement> stats = stat.getStats();
      return !stats.isEmpty() && isTerminating(stats.get(stats.size() - 1));
    }
    // If-else: both branches must terminate
    if (stat.type == Statement.StatementType.IF) {
      IfStatement ifStat = (IfStatement) stat;
      if (ifStat.iftype == IfStatement.IFTYPE_IFELSE
          && ifStat.getIfstat() != null && ifStat.getElsestat() != null) {
        return isTerminating(ifStat.getIfstat()) && isTerminating(ifStat.getElsestat());
      }
    }
    return false;
  }

  /**
   * RTF: fix lambda numbering by swapping if-else branches when the else-body
   * contains lambda expressions with lower bytecode offsets than the if-body's
   * lambdas. javac numbers lambdas by source encounter order, so the branch
   * with the lower-offset lambdas must come first in source.
   */
  private static void fixLambdaOrdering(Statement stat) {
    for (Statement child : new ArrayList<>(stat.getStats())) {
      fixLambdaOrdering(child);
    }

    if (!(stat instanceof IfStatement)) return;
    IfStatement ifStat = (IfStatement) stat;
    if (ifStat.iftype != IfStatement.IFTYPE_IFELSE) return;

    Statement ifBody = ifStat.getIfstat();
    Statement elseBody = ifStat.getElsestat();
    if (ifBody == null || elseBody == null) return;

    // Collect the minimum lambda bytecode offset in each branch
    int minIfOffset = getMinLambdaOffset(ifBody);
    int minElseOffset = getMinLambdaOffset(elseBody);

    // Only act if both branches have lambdas and else has lower offsets
    if (minElseOffset < 0 || minIfOffset < 0) return;
    if (minElseOffset >= minIfOffset) return;

    // Swap bodies
    ifStat.setIfstat(elseBody);
    ifStat.setElsestat(ifBody);
    ifStat.toggleRtfIfBodyIsFallThrough(); // bodies swapped

    // Swap edges
    StatEdge tmpEdge = ifStat.getIfEdge();
    ifStat.setIfEdge(ifStat.getElseEdge());
    ifStat.setElseEdge(tmpEdge);

    // Negate condition
    IfExprent headExpr = ifStat.getHeadexprent();
    Exprent negated = new FunctionExprent(
      FunctionExprent.FunctionType.BOOL_NOT, headExpr.getCondition(), null);
    Exprent simplified = SecondaryFunctionsHelper.propagateBoolNot(negated);
    headExpr.setCondition(simplified != null ? simplified : negated);
  }

  /** Find the minimum bytecode offset of any lambda NewExprent in a statement tree. Returns -1 if none. */
  private static int getMinLambdaOffset(Statement stat) {
    int[] min = {Integer.MAX_VALUE};
    collectLambdaOffsets(stat, min);
    return min[0] == Integer.MAX_VALUE ? -1 : min[0];
  }

  private static void collectLambdaOffsets(Statement stat, int[] min) {
    if (stat.getExprents() != null) {
      for (Exprent expr : stat.getExprents()) {
        collectLambdaOffsetsFromExpr(expr, min);
      }
    }
    for (Exprent expr : stat.getVarDefinitions()) {
      collectLambdaOffsetsFromExpr(expr, min);
    }
    for (Statement child : stat.getStats()) {
      collectLambdaOffsets(child, min);
    }
  }

  private static void collectLambdaOffsetsFromExpr(Exprent expr, int[] min) {
    List<Exprent> all = expr.getAllExprents(true);
    all.add(expr);
    for (Exprent e : all) {
      if (e instanceof NewExprent) {
        NewExprent ne = (NewExprent) e;
        if (ne.isLambda() && ne.bytecode != null) {
          int offset = ne.bytecode.nextSetBit(0);
          if (offset >= 0 && offset < min[0]) {
            min[0] = offset;
          }
        }
      }
    }
  }

  /**
   * RTF: mark all for-each loops to force var for their iteration variable.
   */
  private static void markForEachVar(RootStatement root) {
    markForEachVarRec(root);
  }

  private static void markForEachVarRec(Statement stat) {
    if (stat instanceof DoStatement) {
      DoStatement doStat = (DoStatement) stat;
      if (doStat.getLooptype() == DoStatement.Type.FOR_EACH) {
        doStat.setRtfForceForEachVar(true);
      }
    }
    for (Statement st : stat.getStats()) {
      markForEachVarRec(st);
    }
  }

  /**
   * RTF: hoist super()/this() out of label blocks in constructors.
   * When a label block wraps the entire constructor body, super() ends up inside
   * the block. Java requires super() to be the first statement. This moves
   * super() (and field initializations) from inside the label block to before it.
   */
  private static void hoistSuperFromLabelBlock(RootStatement root) {
    Statement body = root.getFirst();
    // Body is typically a SequenceStatement; the first child may be a labeled BasicBlockStatement
    Statement firstStat = body;
    if (body instanceof SequenceStatement && !body.getStats().isEmpty()) {
      firstStat = body.getStats().get(0);
    }

    // Check if firstStat is labeled
    if (!firstStat.isLabeled()) {
      return;
    }

    // Find the actual basic block containing super() — it may be inside the labeled sequence
    Statement innerBlock = firstStat;
    while (innerBlock.getExprents() == null && !innerBlock.getStats().isEmpty()) {
      innerBlock = innerBlock.getFirst();
    }
    if (innerBlock.getExprents() == null || innerBlock.getExprents().isEmpty()) {
      return;
    }

    Exprent firstExpr = innerBlock.getExprents().get(0);
    if (!(firstExpr instanceof InvocationExprent)) {
      return;
    }
    InvocationExprent invoc = (InvocationExprent) firstExpr;
    if (!invoc.getName().equals("<init>")) {
      return;
    }

    // Found super()/this() inside a labeled block. Hoist it (and field inits) out.
    List<Exprent> toHoist = new ArrayList<>();
    List<Exprent> remaining = new ArrayList<>(innerBlock.getExprents());

    // Hoist super() and subsequent field assignments (this.field = value)
    toHoist.add(remaining.remove(0)); // super()
    while (!remaining.isEmpty()) {
      Exprent next = remaining.get(0);
      if (next instanceof AssignmentExprent) {
        Exprent left = ((AssignmentExprent) next).getLeft();
        if (left instanceof FieldExprent && !((FieldExprent) left).isStatic()) {
          toHoist.add(remaining.remove(0));
          continue;
        }
      }
      break;
    }

    // Put remaining exprents back in the inner block
    innerBlock.getExprents().clear();
    innerBlock.getExprents().addAll(remaining);

    // Insert hoisted exprents as a new BasicBlockStatement before the labeled block
    if (body instanceof SequenceStatement) {
      BasicBlockStatement hoistBlock = BasicBlockStatement.create();
      hoistBlock.setExprents(toHoist);
      body.getStats().addWithKeyAndIndex(0, hoistBlock, hoistBlock.id);
      hoistBlock.setParent(body);
    } else {
      // If body is not a sequence, prepend to varDefinitions
      firstStat.getVarDefinitions().addAll(0, toHoist);
    }
  }

  public RootStatement getResult() throws Throwable {
    Throwable t = error;
    if (t != null) throw t;
    return root;
  }

  public boolean isFinished() {
    return finished;
  }

  /**
   * RTF: re-introduce dead variable-to-variable stores from the original bytecode.
   * Scans the instruction sequence for load+store pairs where the destination slot
   * is never loaded from in the entire method. These are dead stores that Vineflower's
   * SSA optimization eliminated but javac would preserve on recompilation.
   * Adds them as assignments in the first statement's exprents.
   */
  private static boolean reintroduceDeadStores(RootStatement root, StructMethod mt, VarProcessor varProc) {
    InstructionSequence seq = mt.getInstructionSequence();
    if (seq == null) return false;

    // Determine parameter slot range
    MethodDescriptor desc = MethodDescriptor.parseDescriptor(mt.getDescriptor());
    int paramSlotEnd = mt.hasModifier(CodeConstants.ACC_STATIC) ? 0 : 1;
    for (VarType p : desc.params) {
      paramSlotEnd += p.stackSize;
    }

    // Collect all slots that are loaded from (read) anywhere in the bytecode
    Set<Integer> loadedSlots = new HashSet<>();
    for (int i = 0; i < seq.length(); i++) {
      int slot = getLoadSlot(seq.getInstr(i));
      if (slot >= 0) {
        loadedSlots.add(slot);
      }
    }

    // Find load+store pairs where:
    // - Source is a parameter slot (safe to reference at method start)
    // - Destination slot is never loaded from in the method
    // - Source and destination are different slots
    Set<String> seen = new HashSet<>();
    List<int[]> deadStores = new ArrayList<>();
    for (int i = 0; i < seq.length() - 1; i++) {
      Instruction load = seq.getInstr(i);
      Instruction store = seq.getInstr(i + 1);
      int srcSlot = getLoadSlot(load);
      int dstSlot = getStoreSlot(store);
      if (srcSlot >= 0 && dstSlot >= 0 && srcSlot != dstSlot
          && srcSlot < paramSlotEnd
          && !loadedSlots.contains(dstSlot)
          && seen.add(srcSlot + "->" + dstSlot)) {
        deadStores.add(new int[]{srcSlot, dstSlot});
      }
    }

    if (deadStores.isEmpty()) return false;

    // Find the first statement with exprents to insert into
    Statement first = root.getFirst();
    while (first != null && first.getExprents() == null && !first.getStats().isEmpty()) {
      first = first.getFirst();
    }
    if (first == null || first.getExprents() == null) return false;

    boolean changed = false;
    for (int[] ds : deadStores) {
      int srcSlot = ds[0];
      int dstSlot = ds[1];

      // Check that the destination variable doesn't already exist in the AST
      if (isSlotReferencedInAST(root, dstSlot, varProc)) continue;

      // Find the source variable's type from VarProcessor
      VarType srcType = varProc.getVarType(new VarVersionPair(srcSlot, 0));
      if (srcType == null) srcType = VarType.VARTYPE_INT;

      // Create the dead store assignment: dstVar = srcVar
      VarExprent srcVar = new VarExprent(srcSlot, srcType, varProc);
      VarExprent dstVar = new VarExprent(dstSlot, srcType, varProc);
      dstVar.setDefinition(true);
      AssignmentExprent assign = new AssignmentExprent(dstVar, srcVar, null);

      first.getExprents().add(0, assign);
      changed = true;
    }

    return changed;
  }

  /** Get the local variable slot loaded by this instruction, or -1 if not a load. */
  private static int getLoadSlot(Instruction instr) {
    int op = instr.opcode;
    if (op >= CodeConstants.opc_iload && op <= CodeConstants.opc_aload) {
      return instr.operand(0);
    }
    if (op >= CodeConstants.opc_iload_0 && op <= CodeConstants.opc_aload_3) {
      return (op - CodeConstants.opc_iload_0) % 4;
    }
    return -1;
  }

  /** Get the local variable slot stored by this instruction, or -1 if not a store. */
  private static int getStoreSlot(Instruction instr) {
    int op = instr.opcode;
    if (op >= CodeConstants.opc_istore && op <= CodeConstants.opc_astore) {
      return instr.operand(0);
    }
    if (op >= CodeConstants.opc_istore_0 && op <= CodeConstants.opc_astore_3) {
      return (op - CodeConstants.opc_istore_0) % 4;
    }
    return -1;
  }

  /** Check if a bytecode slot is referenced in the final AST (via VarProcessor mapping). */
  private static boolean isSlotReferencedInAST(Statement stat, int slot, VarProcessor varProc) {
    if (stat.getExprents() != null) {
      for (Exprent expr : stat.getExprents()) {
        if (exprReferencesSlot(expr, slot, varProc)) return true;
      }
    }
    for (Exprent expr : stat.getVarDefinitions()) {
      if (exprReferencesSlot(expr, slot, varProc)) return true;
    }
    for (Statement child : stat.getStats()) {
      if (isSlotReferencedInAST(child, slot, varProc)) return true;
    }
    return false;
  }

  private static boolean exprReferencesSlot(Exprent expr, int slot, VarProcessor varProc) {
    if (expr instanceof VarExprent ve) {
      int origSlot = varProc.getOriginalVarIndex(ve.getIndex());
      if (origSlot == slot) return true;
    }
    for (Exprent sub : expr.getAllExprents(true)) {
      if (sub instanceof VarExprent ve) {
        int origSlot = varProc.getOriginalVarIndex(ve.getIndex());
        if (origSlot == slot) return true;
      }
    }
    return false;
  }

}
