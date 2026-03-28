// Copyright 2000_2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.main.rels;

import org.jetbrains.java.decompiler.api.java.JavaPassLocation;
import org.jetbrains.java.decompiler.api.plugin.LanguageSpec;
import org.jetbrains.java.decompiler.api.plugin.pass.PassContext;
import org.jetbrains.java.decompiler.code.CodeConstants;
import org.jetbrains.java.decompiler.code.InstructionSequence;
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
import org.jetbrains.java.decompiler.struct.StructClass;
import org.jetbrains.java.decompiler.struct.StructMethod;
import org.jetbrains.java.decompiler.struct.gen.MethodDescriptor;
import org.jetbrains.java.decompiler.util.DotExporter;
import org.jetbrains.java.decompiler.util.StartEndPair;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

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

}
