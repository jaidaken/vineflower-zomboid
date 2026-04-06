package org.jetbrains.java.decompiler.modules.decompiler.sforms;

import org.jetbrains.java.decompiler.code.CodeConstants;
import org.jetbrains.java.decompiler.code.ExceptionHandler;
import org.jetbrains.java.decompiler.modules.decompiler.ValidationHelper;
import org.jetbrains.java.decompiler.modules.decompiler.exps.*;
import org.jetbrains.java.decompiler.modules.decompiler.flow.*;
import org.jetbrains.java.decompiler.modules.decompiler.stats.*;
import org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionNode;
import org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair;
import org.jetbrains.java.decompiler.struct.StructMethod;
import org.jetbrains.java.decompiler.struct.attr.StructLocalVariableTableAttribute;
import org.jetbrains.java.decompiler.code.Instruction;
import org.jetbrains.java.decompiler.code.InstructionSequence;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.collectors.CounterContainer;
import org.jetbrains.java.decompiler.struct.gen.CodeType;
import org.jetbrains.java.decompiler.struct.gen.MethodDescriptor;
import org.jetbrains.java.decompiler.struct.gen.TypeFamily;
import org.jetbrains.java.decompiler.util.DotExporter;
import org.jetbrains.java.decompiler.util.InterpreterUtil;
import org.jetbrains.java.decompiler.util.collections.FastSparseSetFactory;
import org.jetbrains.java.decompiler.util.collections.FastSparseSetFactory.FastSparseSet;
import org.jetbrains.java.decompiler.util.collections.SFormsFastMapDirect;

import java.util.*;

import static org.jetbrains.java.decompiler.modules.decompiler.sforms.VarMapHolder.mergeMaps;

public abstract class SFormsConstructor {

  @Deprecated(forRemoval = true)
  public final boolean trackFieldVars;
  @Deprecated(forRemoval = true)
  public final boolean trackDirectAssignments;


  // node id, var, version
  private final HashMap<String, SFormsFastMapDirect> inVarVersions = new HashMap<>();

  // node id, var, version (direct branch)
  private final HashMap<String, SFormsFastMapDirect> outVarVersions = new HashMap<>();

  // node id, var, version (negative branch)
  private final HashMap<String, SFormsFastMapDirect> outNegVarVersions = new HashMap<>();

  // node id, var, version
  private final HashMap<String, SFormsFastMapDirect> extraVarVersions = new HashMap<>();

  // node id, var, version
  private final HashMap<String, SFormsFastMapDirect> catchableVersions = new HashMap<>();

  // var, version
  private final HashMap<Integer, Integer> lastversion = new HashMap<>();

  // set factory
  FastSparseSetFactory<Integer> factory;


  private SFormsFastMapDirect currentCatchableMap = null;


  protected RootStatement root;
  private StructMethod mt;
  DirectGraph dgraph;

  public SFormsConstructor(
    boolean trackFieldVars,
    boolean trackDirectAssignments) {
    this.trackFieldVars = trackFieldVars;
    this.trackDirectAssignments = trackDirectAssignments;
  }

  public void splitVariables(RootStatement root, StructMethod mt) {
    this.root = root;
    this.mt = mt;

    FlattenStatementsHelper flatthelper = new FlattenStatementsHelper();
    DirectGraph dgraph = flatthelper.buildDirectGraph(root);
    this.dgraph = dgraph;
    ValidationHelper.validateDGraph(dgraph, root);
    ValidationHelper.validateVars(dgraph, root, var -> var.getVersion() == 0, "Var version is not zero");

    // Pre-split local variable slots that hold different JVM types.
    // Scans raw bytecode to find slots where both FSTORE and ASTORE (or other
    // incompatible store opcodes) are used, then renames the minority VarExprents.
    preSplitIncompatibleSlots(dgraph, mt);

    // FIXME: this overrides the previous iteration
    DotExporter.toDotFile(dgraph, mt, "ssaSplitVariables");

    List<Integer> setInit = new ArrayList<>();
    for (int i = 0; i < 64; i++) {
      setInit.add(i);
    }
    this.factory = new FastSparseSetFactory<>(setInit);

    this.extraVarVersions.put(dgraph.first.id, this.createFirstMap());

    this.setCatchMaps(root, dgraph, flatthelper);

    int iteration = 1;
    Set<String> updated = new HashSet<>();
    do {
      // System.out.println("~~~~~~~~~~~~~ \r\n"+root.toJava());
      this.ssaStatements(dgraph, updated, false, mt, iteration++);
      // System.out.println("~~~~~~~~~~~~~ \r\n"+root.toJava());
    }
    while (!updated.isEmpty());
  }

  /**
   * Scan raw bytecode to find slots where different store opcodes are used
   * (e.g., FSTORE and ASTORE to the same slot). These slots hold different
   * JVM types and must be split into separate variables before SSA.
   *
   * Only splits when the store opcodes use truly different JVM type categories:
   * - ISTORE (int/byte/short/char/boolean) vs FSTORE (float) vs ASTORE (Object) vs LSTORE (long) vs DSTORE (double)
   * ISTORE covers all integer-like types including boolean, so no false splits there.
   */
  private static void preSplitIncompatibleSlots(DirectGraph dgraph, StructMethod mt) {
    InstructionSequence seq = mt.getInstructionSequence();
    if (seq == null) return;

    // Phase 1: Scan bytecode for store opcodes per slot
    // Map slot -> set of store opcode categories (0=istore, 1=lstore, 2=fstore, 3=dstore, 4=astore)
    Map<Integer, Set<Integer>> slotStoreCategories = new HashMap<>();
    for (int i = 0; i < seq.length(); i++) {
      Instruction instr = seq.getInstr(i);
      int category = -1;
      switch (instr.opcode) {
        case CodeConstants.opc_istore: category = 0; break;
        case CodeConstants.opc_lstore: category = 1; break;
        case CodeConstants.opc_fstore: category = 2; break;
        case CodeConstants.opc_dstore: category = 3; break;
        case CodeConstants.opc_astore: category = 4; break;
      }
      if (category >= 0) {
        int slot = instr.operand(0);
        slotStoreCategories.computeIfAbsent(slot, k -> new HashSet<>()).add(category);
      }
    }

    // Phase 2: Find slots with truly incompatible store categories.
    // Only split when FLOAT (2) coexists with OBJECT (4), or DOUBLE (3) with OBJECT (4).
    // ISTORE (0) is compatible with everything (null/boolean patterns use astore then istore).
    Set<Integer> conflictSlots = new HashSet<>();
    for (Map.Entry<Integer, Set<Integer>> entry : slotStoreCategories.entrySet()) {
      Set<Integer> cats = entry.getValue();
      boolean hasInt = cats.contains(0);    // istore
      boolean hasFloat = cats.contains(2);  // fstore
      boolean hasDouble = cats.contains(3); // dstore
      boolean hasObject = cats.contains(4); // astore
      // FLOAT+OBJECT or DOUBLE+OBJECT: always split
      if ((hasFloat && hasObject) || (hasDouble && hasObject)) {
        conflictSlots.add(entry.getKey());
      }
      // INT+OBJECT: split when the slot has BOTH astore (String/Object value) AND
      // istore (int value) with BOTH aload and iload, AND the method has a switch instruction.
      if (hasInt && hasObject) {
        int slot = entry.getKey();
        boolean hasAload = false, hasIload = false, hasSwitch = false;
        for (int si = 0; si < seq.length(); si++) {
          Instruction si_instr = seq.getInstr(si);
          if (si_instr.opcode == CodeConstants.opc_aload && si_instr.operand(0) == slot) hasAload = true;
          if (si_instr.opcode == CodeConstants.opc_iload && si_instr.operand(0) == slot) hasIload = true;
          if (si_instr.opcode == CodeConstants.opc_lookupswitch || si_instr.opcode == CodeConstants.opc_tableswitch) hasSwitch = true;
        }
        if (hasAload && hasIload && hasSwitch) {
          conflictSlots.add(slot);
        }
      }
    }

    // Phase 2b: LVT-based slot reuse detection.
    // Handles two patterns where the JVM reuses a slot for different variables:
    //
    // Pattern A (OBJECT+OBJECT): slot has only astore, but some astores are at
    // bytecode offsets significantly before the earliest LVT entry for the slot.
    // Example: rawget() stored to slot, checked with instanceof, then slot reused
    // for an iterator or typed variable declared later.
    //
    // Pattern B (INT+OBJECT after LVT): slot has both istore and astore, and
    // some istores are at offsets significantly after the last LVT entry for the
    // slot. Example: BufferedReader in try block (covered by LVT), then boolean
    // in catch block (istore after LVT range ends).
    Set<Integer> lvtConflictSlots = new HashSet<>();
    StructLocalVariableTableAttribute lvtAttr = mt.getLocalVariableAttr();
    if (lvtAttr != null) {
      Set<Integer> handlerTargetOffsets = new HashSet<>();
      for (ExceptionHandler handler : seq.getExceptionTable().getHandlers()) {
        handlerTargetOffsets.add(handler.handler);
      }

      for (Map.Entry<Integer, Set<Integer>> entry : slotStoreCategories.entrySet()) {
        int slot = entry.getKey();
        Set<Integer> cats = entry.getValue();
        if (conflictSlots.contains(slot)) continue;

        List<StructLocalVariableTableAttribute.LocalVariable> lvtEntries = new ArrayList<>();
        lvtAttr.matchingVars(slot).forEach(lvtEntries::add);
        if (lvtEntries.isEmpty()) continue;

        // Find earliest LVT start and latest LVT end for this slot
        int earliestStart = Integer.MAX_VALUE;
        int latestEnd = Integer.MIN_VALUE;
        for (StructLocalVariableTableAttribute.LocalVariable lv : lvtEntries) {
          if (lv.getStart() < earliestStart) earliestStart = lv.getStart();
          if (lv.getEnd() > latestEnd) latestEnd = lv.getEnd();
        }

        boolean hasUncoveredStore = false;

        // Pattern A: astore-only slot with uncovered astore before earliest LVT start,
        // AND the stored value is immediately checked with instanceof/checkcast.
        // This catches rawget()+instanceof patterns where the slot holds a temporary
        // Object that's checked before the slot is reused for a typed variable.
        if (cats.size() == 1 && cats.contains(4)) {
          for (int si = 0; si < seq.length(); si++) {
            Instruction si_instr = seq.getInstr(si);
            if (si_instr.opcode != CodeConstants.opc_astore || si_instr.operand(0) != slot) continue;
            int offset = seq.getOffset(si);
            if (handlerTargetOffsets.contains(offset)) continue;
            if (offset < earliestStart - 15) {
              // Verify: the stored value must be loaded and checked with instanceof
              // or checkcast within the next few instructions
              for (int ci = si + 1; ci < Math.min(si + 5, seq.length()); ci++) {
                Instruction check = seq.getInstr(ci);
                if (check.opcode == CodeConstants.opc_instanceof
                    || check.opcode == CodeConstants.opc_checkcast) {
                  hasUncoveredStore = true;
                  break;
                }
              }
              if (hasUncoveredStore) break;
            }
          }
        }

        // Pattern B: INT+OBJECT slot with istore far after last LVT end.
        // This catches try/catch slot reuse where a resource (e.g. BufferedReader)
        // is in the try block (covered by LVT) and a boolean/int is stored in a
        // catch block (istore well after LVT range ends).
        if (!hasUncoveredStore && cats.contains(0) && cats.contains(4)) {
          for (int si = 0; si < seq.length(); si++) {
            Instruction si_instr = seq.getInstr(si);
            if (si_instr.opcode != CodeConstants.opc_istore || si_instr.operand(0) != slot) continue;
            int offset = seq.getOffset(si);
            if (offset > latestEnd + 50) {
              hasUncoveredStore = true;
              break;
            }
          }
        }

        if (hasUncoveredStore) {
          lvtConflictSlots.add(slot);
        }
      }
    }

    if (conflictSlots.isEmpty() && lvtConflictSlots.isEmpty()) return;

    // Phase 3-4: Category-based splitting for INT+OBJECT and FLOAT/DOUBLE+OBJECT conflicts
    if (!conflictSlots.isEmpty()) {
      Map<Integer, Map<Integer, List<VarExprent>>> slotCategoryVars = new HashMap<>();
      dgraph.iterateExprents(exprent -> {
        List<Exprent> lst = exprent.getAllExprents(true);
        lst.add(exprent);
        for (Exprent expr : lst) {
          if (expr instanceof VarExprent) {
            VarExprent var = (VarExprent) expr;
            int idx = var.getIndex();
            if (!conflictSlots.contains(idx)) continue;
            int cat = typeFamilyToStoreCategory(var.getBytecodeTypeFamily());
            if (cat >= 0) {
              slotCategoryVars.computeIfAbsent(idx, k -> new HashMap<>())
                              .computeIfAbsent(cat, k -> new ArrayList<>()).add(var);
            }
          }
        }
        return 0;
      });

      CounterContainer counters = DecompilerContext.getCounterContainer();
      for (int slot : conflictSlots) {
        Map<Integer, List<VarExprent>> categoryVars = slotCategoryVars.get(slot);
        if (categoryVars == null || categoryVars.size() <= 1) continue;

        int majorCat = -1;
        int maxCount = 0;
        for (Map.Entry<Integer, List<VarExprent>> e : categoryVars.entrySet()) {
          if (e.getValue().size() > maxCount) {
            maxCount = e.getValue().size();
            majorCat = e.getKey();
          }
        }

        for (Map.Entry<Integer, List<VarExprent>> e : categoryVars.entrySet()) {
          if (e.getKey() == majorCat) continue;
          int newIdx = counters.getCounterAndIncrement(CounterContainer.VAR_COUNTER);
          for (VarExprent var : e.getValue()) {
            var.setIndex(newIdx);
          }
        }
      }
    }

    // Phase 5: LVT-based splitting for slot reuse.
    // VarExprents whose bytecode offsets fall outside all LVT ranges get new indices.
    if (!lvtConflictSlots.isEmpty() && lvtAttr != null) {
      Map<Integer, List<VarExprent>> uncoveredVars = new HashMap<>();

      dgraph.iterateExprents(exprent -> {
        List<Exprent> lst = exprent.getAllExprents(true);
        lst.add(exprent);
        for (Exprent expr : lst) {
          if (expr instanceof VarExprent) {
            VarExprent var = (VarExprent) expr;
            int idx = var.getIndex();
            if (!lvtConflictSlots.contains(idx)) continue;

            int bcOffset = var.bytecode != null ? var.bytecode.nextSetBit(0) : -1;
            if (bcOffset < 0) {
              uncoveredVars.computeIfAbsent(idx, k -> new ArrayList<>()).add(var);
              continue;
            }

            boolean covered = false;
            for (StructLocalVariableTableAttribute.LocalVariable lv :
                (Iterable<StructLocalVariableTableAttribute.LocalVariable>) () -> lvtAttr.matchingVars(idx).iterator()) {
              if (bcOffset >= lv.getStart() - 15 && bcOffset < lv.getEnd()) {
                covered = true;
                break;
              }
            }
            if (!covered) {
              uncoveredVars.computeIfAbsent(idx, k -> new ArrayList<>()).add(var);
            }
          }
        }
        return 0;
      });

      CounterContainer counters = DecompilerContext.getCounterContainer();
      for (int slot : lvtConflictSlots) {
        List<VarExprent> uncovered = uncoveredVars.get(slot);
        if (uncovered == null || uncovered.isEmpty()) continue;
        int newIdx = counters.getCounterAndIncrement(CounterContainer.VAR_COUNTER);
        for (VarExprent var : uncovered) {
          var.setIndex(newIdx);
        }
      }
    }
  }

  /**
   * Map a TypeFamily to a store category (matching bytecode store opcodes).
   * Returns: 0=istore, 1=lstore, 2=fstore, 3=dstore, 4=astore, -1=unknown
   */
  private static int typeFamilyToStoreCategory(TypeFamily family) {
    if (family == null) return -1;
    switch (family) {
      case BOOLEAN:
      case INTEGER:
        return 0; // istore
      case LONG:
        return 1; // lstore
      case FLOAT:
        return 2; // fstore
      case DOUBLE:
        return 3; // dstore
      case OBJECT:
        return 4; // astore
      default:
        return -1;
    }
  }

  void ssaStatements(DirectGraph dgraph, Set<String> updated, boolean calcLiveVars, StructMethod mt, int iteration) {

    DotExporter.toDotFile(dgraph, mt, "ssaStatements_" + iteration, this.outVarVersions);

    for (DirectNode node : dgraph.nodes) {

      updated.remove(node.id);
      this.mergeInVarMaps(node, dgraph);

      SFormsFastMapDirect varmap = this.inVarVersions.get(node.id);
      VarMapHolder varmaps = VarMapHolder.ofNormal(varmap);
      this.currentCatchableMap = null;

      if (node.hasSuccessors(DirectEdgeType.EXCEPTION)) {
        this.currentCatchableMap = varmap.getCopy();
        this.currentCatchableMap.removeAllStacks(); // stack gets cleared when throwing
        this.currentCatchableMap.removeAllFields(); // fields gets invalidated when throwing
        this.catchableVersions.put(node.id, this.currentCatchableMap);
      }

      // Foreach init node: mark as assignment!
      if (node.type == DirectNodeType.FOREACH_VARDEF && node.exprents.get(0) instanceof VarExprent) {
        this.updateVarExprent((VarExprent) node.exprents.get(0), node.statement, varmaps.getNormal(), calcLiveVars);
      } else if (node.exprents != null) {
        for (Exprent expr : node.exprents) {
          varmaps.toNormal(); // make sure we are in normal form
          expr.processSforms(this, varmaps, node.statement, calcLiveVars);
        }
      }

      if (this.hasUpdated(node, varmaps)) {
        this.outVarVersions.put(node.id, varmaps.getIfTrue());
        if (dgraph.mapNegIfBranch.containsKey(node.id)) {
          this.outNegVarVersions.put(node.id, varmaps.getIfFalse());
        }

        // Don't update the node if it wasn't discovered normally, as that can lead to infinite recursion due to bad ordering!
        if (!dgraph.extraNodes.contains(node)) {
          for (DirectEdge nd : node.getSuccessors(DirectEdgeType.REGULAR)) {
            updated.add(nd.getDestination().id);
          }

          for (DirectEdge nd : node.getSuccessors(DirectEdgeType.EXCEPTION)) {
            updated.add(nd.getDestination().id);
          }
        }
      }
    }
  }

  abstract public VarVersionPair getOrCreatePhantom(VarVersionPair var);

  public void varRead(VarMapHolder varMaps, Statement stat, boolean calcLiveVars, VarExprent varExprent) {
    final SFormsFastMapDirect varmap = varMaps.getNormal();

    FastSparseSet<Integer> versions = varmap.get(varExprent);

    int cardinality = versions != null ? versions.getCardinality() : 0;
    switch (cardinality) {
      case 0: { // size == 0 (var has no discovered assignments yet)
        // TODO: shouldn't every path from the start of the method to a variable usage have an assignment?
        //   seems to trigger with enhanced switches
        this.updateVarExprent(varExprent, stat, varmap, calcLiveVars);
        ValidationHelper.validateTrue(false, "Variable read before assignment: " + varExprent);
        break;
      }
      case 1: { // size == 1 (var has only one discovered assignment)
        this.varReadSingleVersion(stat, calcLiveVars, varExprent, varmap, versions.iterator().next());
        break;
      }
      case 2:  // size > 1 (var has more than one assignment)
        this.varReadMultipleVersions(stat, calcLiveVars, varExprent, varmap, versions);
        break;
    }
  }

  abstract void varReadSingleVersion(
    Statement stat,
    boolean calcLiveVars,
    VarExprent varExprent,
    SFormsFastMapDirect varmap,
    int lastVersion);

  abstract void varReadMultipleVersions(
    Statement stat,
    boolean calcLiveVars,
    VarExprent varExprent,
    SFormsFastMapDirect varMap,
    FastSparseSet<Integer> versions);

  public abstract void markDirectAssignment(VarVersionPair varVersionPair, VarVersionPair rightPair);


  private static boolean makesFieldsDirty(Exprent expr) {
    switch (expr.type) {
      case INVOCATION:
        return true;
      case NEW:
        if (((NewExprent) expr).getNewType().type == CodeType.OBJECT) {
          return true;
        }
        break;
    }
    return false;
  }

  abstract void initVersion(VarExprent varExprent, Statement stat);

  // Declaration of a variable
  public void updateVarExprent(VarExprent varassign, Statement stat, SFormsFastMapDirect varmap, boolean calcLiveVars) {
    int varIndex = varassign.getIndex();

    this.initVersion(varassign, stat);

    this.onAssignment(varassign.getVarVersionPair(), varmap, calcLiveVars);

    this.setCurrentVar(varmap, varIndex, varassign.getVersion());

    // update catchables map for normal vars only
    if (this.currentCatchableMap != null && varIndex < VarExprent.STACK_BASE && varIndex >= 0) {

      if (this.currentCatchableMap.containsKey(varIndex)) {
        this.currentCatchableMap.get(varIndex).add(varassign.getVersion());
      } else {
        FastSparseSet<Integer> set = this.factory.createEmptySet();
        set.add(varassign.getVersion());
        varmap.put(varIndex, set);
      }
    }
  }

  // TODO: make calcLiveVars a field in SSAU
  protected void onAssignment(VarVersionPair varVersionPair, SFormsFastMapDirect varMap, boolean calcLiveVars) {

  }

  private void mergeInVarMaps(DirectNode node, DirectGraph dgraph) {

    SFormsFastMapDirect mapNew = new SFormsFastMapDirect(this.factory);

    for (DirectEdge pred : node.getPredecessors(DirectEdgeType.REGULAR)) {
      SFormsFastMapDirect mapOut = this.getFilteredOutMap(node, pred.getSource(), dgraph);
      if (mapNew.isEmpty()) {
        mapNew = mapOut.getCopy();
      } else {
        mergeMaps(mapNew, mapOut);
      }
    }

    for (DirectEdge pred : node.getPredecessors(DirectEdgeType.EXCEPTION)) {
      // TODO: interact with finally?
      SFormsFastMapDirect mapOut = this.catchableVersions.get(pred.getSource().id);
      if (mapOut != null) {
        if (mapNew.isEmpty()) {
          mapNew = mapOut.getCopy();
        } else {
          mergeMaps(mapNew, mapOut);
        }
      }
    }

    if (this.extraVarVersions.containsKey(node.id)) {
      SFormsFastMapDirect mapExtra = this.extraVarVersions.get(node.id);
      if (mapNew.isEmpty()) {
        mapNew = mapExtra.getCopy();
      } else {
        mergeMaps(mapNew, mapExtra);
      }
    }

    this.inVarVersions.put(node.id, mapNew);
  }

  private SFormsFastMapDirect getFilteredOutMap(DirectNode node, DirectNode pred, DirectGraph dgraph) {

    SFormsFastMapDirect mapNew = new SFormsFastMapDirect(this.factory);

    if (node.id.equals(dgraph.mapNegIfBranch.get(pred.id))) {
      if (this.outNegVarVersions.containsKey(pred.id)) {
        mapNew = this.outNegVarVersions.get(pred.id).getCopy();
      }
    } else if (this.outVarVersions.containsKey(pred.id)) {
      mapNew = this.outVarVersions.get(pred.id).getCopy();
    }

    // handle finally
    if (node.tryFinally != pred.tryFinally) {
      if (node.tryFinally != null &&
        node.tryFinally.type == DirectNodeType.FINALLY &&
        node.tryFinally.tryFinally == pred.tryFinally) {
        // we are entering a try, nothing to do here
      } else if (pred.type == DirectNodeType.FINALLY) {
        // we are entering the finally block
      } else {
        DirectNode finallyNode = pred.tryFinally;
        while (finallyNode != node.tryFinally) {
          ValidationHelper.notNull(finallyNode);
          if (finallyNode.type == DirectNodeType.FINALLY) {

            getAndApplyDiff(this.inVarVersions.get(finallyNode.statement.id + "_FINALLY"), this.outVarVersions.get(finallyNode.id), mapNew);

          }
          finallyNode = finallyNode.tryFinally;
        }
      }
    }

    return mapNew;
  }

  private static void getAndApplyDiff(SFormsFastMapDirect input, SFormsFastMapDirect output, SFormsFastMapDirect target) {
    if (input == null || output == null) {
      return;
    }

    for (Map.Entry<Integer, FastSparseSet<Integer>> entry : input.entryList()) {
      Integer key = entry.getKey();

      if (key >= VarExprent.STACK_BASE) {
        continue;
      }

      if (entry.getValue().isEmpty()) {
        continue;
      }

      Integer first = entry.getValue().iterator().next();
      if (output.containsKey(key)) {
        if (output.get(key).contains(first)) {
          // the input is still readable
          FastSparseSet<Integer> check = output.get(key).getCopy();
          check.complement(entry.getValue());
          if (check.isEmpty()) {
            // no writes happened, do nothing
          } else {
            // some writes happened, append the additional writes
            target.get(key).union(check);
          }
        } else {
          // the input is not readable anymore, only set the writes
          target.put(key, entry.getValue().getCopy());
        }
      }
    }

    for (Map.Entry<Integer, FastSparseSet<Integer>> entry : output.entryList()) {
      Integer key = entry.getKey();

      if (key >= VarExprent.STACK_BASE) {
        continue;
      }

      if (entry.getValue().isEmpty()) {
        continue;
      }

      if (input.containsKey(key) && !input.get(key).isEmpty()) {
        continue; // already handled
      }

      // set the writes in the output
      target.put(key, entry.getValue().getCopy());
    }
  }

  public static Statement getFirstProtectedRange(Statement stat) {
    while (true) {
      Statement parent = stat.getParent();

      if (parent == null) {
        break;
      }

      if (parent instanceof CatchAllStatement || parent instanceof CatchStatement) {
        if (parent.getFirst() == stat) {
          return parent;
        }
      } else if (parent instanceof SynchronizedStatement) {
        if (((SynchronizedStatement) parent).getBody() == stat) {
          return parent;
        }
      }

      stat = parent;
    }

    return null;
  }

  // TODO: these could instead be VarExprents / PatternExprents in the catch dnode
  private void setCatchMaps(Statement stat, DirectGraph dgraph, FlattenStatementsHelper flatthelper) {

    SFormsFastMapDirect map;

    switch (stat.type) {
      case CATCH_ALL:
      case TRY_CATCH:

        List<VarExprent> lstVars;
        if (stat instanceof CatchAllStatement) {
          lstVars = ((CatchAllStatement) stat).getVars();
        } else {
          lstVars = ((CatchStatement) stat).getVars();
        }

        for (int i = 1; i < stat.getStats().size(); i++) {
          int varindex = lstVars.get(i - 1).getIndex();
          map = new SFormsFastMapDirect(this.factory);

          this.initParameter(varindex, map, true);

          this.extraVarVersions.put(flatthelper.getDirectNode(stat.getStats().get(i)).id, map);

        }
    }

    for (Statement st : stat.getStats()) {
      this.setCatchMaps(st, dgraph, flatthelper);
    }
  }

  private SFormsFastMapDirect createFirstMap() {
    boolean hasThis = !this.mt.hasModifier(CodeConstants.ACC_STATIC);

    MethodDescriptor md = MethodDescriptor.parseDescriptor(this.mt.getDescriptor());

    int paramCount = md.params.length + (hasThis ? 1 : 0);

    SFormsFastMapDirect varMap = new SFormsFastMapDirect(this.factory);
    for (int varIndex = 0, i = 0; i < paramCount; i++) {
      this.initParameter(varIndex, varMap, false);

      if (hasThis) {
        if (i == 0) {
          varIndex++;
        } else {
          varIndex += md.params[i - 1].stackSize;
        }
      } else {
        varIndex += md.params[i].stackSize;
      }
    }

    return varMap;
  }

  abstract public void initParameter(int varIndex, SFormsFastMapDirect varMap, boolean isCatchVar);

  public static void makeReadEdge(VarVersionNode phiNode, VarVersionNode tempNode) {
    tempNode.successors.add(phiNode);
    phiNode.predecessors.add(tempNode);
  }


  static boolean mapsEqual(SFormsFastMapDirect map1, SFormsFastMapDirect map2) {

    if (map1 == null) {
      return map2 == null;
    } else if (map2 == null) {
      return false;
    }

    if (map1.size() != map2.size()) {
      return false;
    }

    for (Map.Entry<Integer, FastSparseSet<Integer>> ent2 : map2.entryList()) {
      if (!InterpreterUtil.equalObjects(map1.get(ent2.getKey()), ent2.getValue())) {
        return false;
      }
    }

    return true;
  }

  public void fieldRead(FieldExprent field, SFormsFastMapDirect varmap) {
    // a read of a field variable.
    if (this.trackFieldVars) {
      int index = this.getFieldIndex(field);

      varmap.setCurrentVar(index, 1);
    }
  }

  @Deprecated
  void setCurrentVar(SFormsFastMapDirect varmap, int var, int vers) {
    FastSparseSet<Integer> set = this.factory.createEmptySet();
    set.add(vers);
    varmap.put(var, set);
  }

  boolean hasUpdated(DirectNode node, VarMapHolder varmaps) {
    return !mapsEqual(varmaps.getIfTrue(), this.outVarVersions.get(node.id))
      || (this.outNegVarVersions.containsKey(node.id) && !mapsEqual(varmaps.getIfFalse(), this.outNegVarVersions.get(node.id)));
  }

  public abstract Integer getFieldIndex(FieldExprent field);

  protected int getNextFreeVersion(int var, Statement stat) {
    return this.lastversion.compute(var, (k, v) -> v == null ? 1 : v + 1);
  }
  
  public DirectGraph getDirectGraph() {
    return this.dgraph;
  }
}
