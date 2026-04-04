// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.modules.decompiler;

import org.jetbrains.java.decompiler.code.cfg.BasicBlock;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.collectors.CounterContainer;
import org.jetbrains.java.decompiler.code.CodeConstants;
import org.jetbrains.java.decompiler.code.Instruction;
import org.jetbrains.java.decompiler.code.InstructionSequence;
import org.jetbrains.java.decompiler.main.rels.MethodWrapper;
import org.jetbrains.java.decompiler.modules.decompiler.exps.ConstExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.ExitExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.Exprent;
import org.jetbrains.java.decompiler.modules.decompiler.stats.*;
import org.jetbrains.java.decompiler.modules.decompiler.stats.Statement.EdgeDirection;
import org.jetbrains.java.decompiler.struct.gen.CodeType;
import org.jetbrains.java.decompiler.struct.gen.MethodDescriptor;
import org.jetbrains.java.decompiler.struct.gen.VarType;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Set;

public final class ExitHelper {
  public static boolean condenseExits(RootStatement root) {
    int changed = integrateExits(root);

    if (changed > 0) {
      cleanUpUnreachableBlocks(root);
      SequenceHelper.condenseSequences(root);
    }

    return (changed > 0);
  }

  private static void cleanUpUnreachableBlocks(Statement stat) {
    boolean found;
    do {
      found = false;

      for (int i = 0; i < stat.getStats().size(); i++) {
        Statement st = stat.getStats().get(i);

        cleanUpUnreachableBlocks(st);

        if (st instanceof SequenceStatement && st.getStats().size() > 1) {

          Statement last = st.getStats().getLast();
          Statement secondlast = st.getStats().get(st.getStats().size() - 2);

          if (!hasEffectiveBasicSuccEdge(secondlast)) {
            Set<Statement> set = last.getNeighboursSet(Statement.STATEDGE_DIRECT_ALL, EdgeDirection.BACKWARD);
            set.remove(secondlast);

            if (set.isEmpty()) {
              last.getExprents().clear();
              st.getStats().removeWithKey(last.id);
              for (StatEdge succEdge : last.getAllSuccessorEdges()) {
                succEdge.remove();
              }
              for (StatEdge predEdge : last.getAllPredecessorEdges()) {
                predEdge.remove();
              }
              found = true;
              break;
            }
          }
        }
      }
    }
    while (found);
  }

  // Turns break edges into returns where possible.
  //
  // Example:
  //
  // label1: {
  //   if (...) {
  //     break label1;
  //   }
  //   ...
  // }
  // return;
  //
  // will turn into
  //
  // if (...) {
  //   return;
  // }
  // ...
  //
  private static int integrateExits(Statement stat) {
    int ret = 0;
    Statement dest;

    if (stat.getExprents() == null) {
      while (true) {
        int changed = 0;

        for (Statement st : stat.getStats()) {
          changed = integrateExits(st);
          if (changed > 0) {
            ret = 1;
            break;
          }
        }

        if (changed == 0) {
          break;
        }
      }

      if (stat instanceof IfStatement) {
        IfStatement ifst = (IfStatement) stat;
        if (ifst.getIfstat() == null) {
          StatEdge ifedge = ifst.getIfEdge();
          dest = isExitEdge(ifedge);
          if (dest != null) {
            BasicBlockStatement bstat = BasicBlockStatement.create();
            bstat.setExprents(DecHelper.copyExprentList(dest.getExprents()));

            ifst.getFirst().removeSuccessor(ifedge);
            StatEdge newedge = new StatEdge(StatEdge.TYPE_REGULAR, ifst.getFirst(), bstat);
            ifst.getFirst().addSuccessor(newedge);
            ifst.setIfEdge(newedge);
            ifst.setIfstat(bstat);
            ifst.getStats().addWithKey(bstat, bstat.id);
            bstat.setParent(ifst);

            StatEdge oldexitedge = dest.getFirstSuccessor();
            StatEdge newexitedge = new StatEdge(StatEdge.TYPE_BREAK, bstat, oldexitedge.getDestination());
            bstat.addSuccessor(newexitedge);
            oldexitedge.closure.addLabeledEdge(newexitedge);
            ret = 1;
          }
        }
      }
    }


    if (stat.getAllSuccessorEdges().size() == 1 &&
        stat.getAllSuccessorEdges().get(0).getType() == StatEdge.TYPE_BREAK &&
        stat.getLabelEdges().isEmpty()) {
      Statement parent = stat.getParent();
      if (stat != parent.getFirst() || !(parent instanceof IfStatement ||
                                         parent instanceof SwitchStatement)) {

        StatEdge destedge = stat.getAllSuccessorEdges().get(0);
        dest = isExitEdge(destedge);
        if (dest != null) {
          // RTF: don't inline return into a try body when the original had a goto
          // exiting the exception range. The return should stay outside the try.
          if (DecompilerContext.isRoundtripFidelity() && rtfContainsGotoExitsTryBody(stat)) {
            dest = null;
          }
        }
        if (dest != null) {
          stat.removeSuccessor(destedge);

          BasicBlockStatement bstat = BasicBlockStatement.create();
          bstat.setExprents(DecHelper.copyExprentList(dest.getExprents()));

          StatEdge oldexitedge = dest.getAllSuccessorEdges().get(0);
          StatEdge newexitedge = new StatEdge(StatEdge.TYPE_BREAK, bstat, oldexitedge.getDestination());
          bstat.addSuccessor(newexitedge);
          oldexitedge.closure.addLabeledEdge(newexitedge);

          SequenceStatement block = new SequenceStatement(Arrays.asList(stat, bstat));
          block.setAllParent();

          parent.replaceStatement(stat, block);
          // LabelHelper.lowContinueLabels not applicable because of forward continue edges
          // LabelHelper.lowContinueLabels(block, new HashSet<StatEdge>());
          // do it by hand
          for (StatEdge prededge : block.getPredecessorEdges(StatEdge.TYPE_CONTINUE)) {
            block.removePredecessor(prededge);
            prededge.getSource().changeEdgeNode(EdgeDirection.FORWARD, prededge, stat);
            stat.addPredecessor(prededge);
            stat.addLabeledEdge(prededge);
          }

          stat.addSuccessor(new StatEdge(StatEdge.TYPE_REGULAR, stat, bstat));

          for (StatEdge edge : dest.getAllPredecessorEdges()) {
            if (!edge.explicit && stat.containsStatementStrict(edge.getSource()) &&
                MergeHelper.isDirectPath(edge.getSource().getParent(), bstat)) {

              dest.removePredecessor(edge);
              edge.getSource().changeEdgeNode(EdgeDirection.FORWARD, edge, bstat);
              bstat.addPredecessor(edge);

              if (!stat.containsStatementStrict(edge.closure)) {
                stat.addLabeledEdge(edge);
              }
            }
          }

          ret = 2;
        }
      }
    }

    return ret;
  }

  /**
   * Check if a statement effectively has a basic successor edge.
   * For most statements, this delegates to hasBasicSuccEdge().
   * For SequenceStatements, we additionally check the last child:
   * a sequence ending with an IfStatement (if-then, no else) or a
   * non-infinite DoStatement DOES have a fall-through path, even though
   * SequenceStatement.hasBasicSuccEdge() returns false by default.
   * This prevents cleanUpUnreachableBlocks from incorrectly removing
   * loop increments that follow wrapper sequences created by integrateExits.
   */
  private static boolean hasEffectiveBasicSuccEdge(Statement stat) {
    if (stat.hasBasicSuccEdge()) {
      return true;
    }
    // SequenceStatement: delegate to last child (a sequence ending with a
    // non-infinite loop or if-then effectively has a fall-through path)
    if (stat instanceof SequenceStatement && !stat.getStats().isEmpty()) {
      return hasEffectiveBasicSuccEdge(stat.getStats().getLast());
    }
    // INFINITE DoStatement: check if the loop has break edges going out,
    // meaning it will later be converted to WHILE/FOR by enhanceLoops.
    // At this point in the pipeline, the loop is still INFINITE but
    // structurally has an exit path.
    if (stat instanceof DoStatement && ((DoStatement) stat).getLooptype() == DoStatement.Type.INFINITE) {
      // An infinite loop with outgoing break edges or with a first-if that
      // could become a while condition effectively has a successor.
      if (!stat.getSuccessorEdges(StatEdge.TYPE_REGULAR).isEmpty()) {
        return true;
      }
      // Check if the loop body starts with an if-break pattern (future while)
      Statement first = stat.getFirst();
      if (first instanceof IfStatement) {
        IfStatement ifst = (IfStatement) first;
        if (ifst.getIfstat() == null) {
          // negated if with break → will become while condition
          return true;
        }
      }
      // Check nested: loop body might be a sequence starting with if-break
      if (first instanceof SequenceStatement && !first.getStats().isEmpty()) {
        Statement seqFirst = first.getStats().get(0);
        if (seqFirst instanceof IfStatement && ((IfStatement) seqFirst).getIfstat() == null) {
          return true;
        }
      }
    }
    return false;
  }

  private static Statement isExitEdge(StatEdge edge) {
    Statement dest = edge.getDestination();

    if (edge.getType() == StatEdge.TYPE_BREAK && dest instanceof BasicBlockStatement && edge.explicit && (edge.labeled || isOnlyEdge(edge)) && edge.canInline) {
      List<Exprent> data = dest.getExprents();

      if (data != null && data.size() == 1) {
        if (data.get(0) instanceof ExitExprent) {
          return dest;
        }
      }
    }

    return null;
  }

  /**
   * RTF: check if any BasicBlock in the statement has rtfGotoExitsTryBody set.
   */
  private static boolean rtfContainsGotoExitsTryBody(Statement stat) {
    if (stat instanceof BasicBlockStatement bbs) {
      return bbs.getBlock().rtfGotoExitsTryBody;
    }
    for (Statement child : stat.getStats()) {
      if (rtfContainsGotoExitsTryBody(child)) return true;
    }
    return false;
  }

  private static boolean isOnlyEdge(StatEdge edge) {
    Statement stat = edge.getDestination();

    for (StatEdge ed : stat.getAllPredecessorEdges()) {
      if (ed != edge) {
        if (ed.getType() == StatEdge.TYPE_REGULAR) {
          Statement source = ed.getSource();

          if (source instanceof BasicBlockStatement || (source instanceof IfStatement &&
                                                        ((IfStatement) source).iftype == IfStatement.IFTYPE_IF) ||
              (source instanceof DoStatement && ((DoStatement) source).getLooptype() != DoStatement.Type.INFINITE)) {
            return false;
          }
        } else {
          return false;
        }
      }
    }

    return true;
  }

  // Removes return statements from the ends of methods when they aren't returning a value
  public static boolean removeRedundantReturns(RootStatement root) {
    boolean res = false;
    DummyExitStatement dummyExit = root.getDummyExit();

    for (StatEdge edge : dummyExit.getAllPredecessorEdges()) {
      if (!edge.explicit) {
        Statement source = edge.getSource();
        List<Exprent> lstExpr = source.getExprents();
        if (lstExpr != null && !lstExpr.isEmpty()) {
          Exprent expr = lstExpr.get(lstExpr.size() - 1);
          if (expr instanceof ExitExprent) {
            ExitExprent ex = (ExitExprent) expr;
            if (ex.getExitType() == ExitExprent.Type.RETURN && ex.getValue() == null) {
              // RTF: preserve void returns inside guard clause IfStatements where
              // both branches terminate. The 2 returns are needed for byte-exact match.
              if (DecompilerContext.isRoundtripFidelity()) {
                if (rtfIsGuardClauseReturn(source, ex)) {
                  continue;
                }
              }
              // remove redundant return
              dummyExit.addBytecodeOffsets(ex.bytecode);
              lstExpr.remove(lstExpr.size() - 1);
              res = true;
            }
          }
        }
      }
    }

    return res;
  }

  /**
   * RTF: check if a statement's void return should be preserved because it's
   * inside a guard clause IfStatement where both branches terminate. Walking
   * up the parent chain, look for an IfStatement with rtfBothBranchesTerminate
   * (and not rtfOriginalHadGotoFallthrough, which is handled separately).
   */
  private static boolean rtfIsGuardClauseReturn(Statement source, ExitExprent ex) {
    // Check for method-end return following a CatchStatement. When the catch body's
    // return is preserved, the method-end return must also be preserved so javac
    // produces 2 returns (no goto needed to skip the catch handler).
    Statement parent = source.getParent();
    if (source instanceof BasicBlockStatement) {
      List<Exprent> srcExprents = source.getExprents();
      if (srcExprents != null && srcExprents.size() == 1 && parent instanceof SequenceStatement) {
        SequenceStatement seq = (SequenceStatement) parent;
        int idx = seq.getStats().getIndexByKey(source.id);
        if (idx > 0) {
          Statement prev = seq.getStats().get(idx - 1);
          if (prev instanceof CatchStatement || prev instanceof CatchAllStatement) {
            if (rtfOriginalWasReturn(ex)) {
              return true;
            }
          }
        }
      }
    }

    // Check for try-catch pattern: return at the end of a try body or catch body.
    // The original has separate returns for each path; javac would share them.
    // Walk up through SequenceStatements to find a CatchStatement ancestor.
    if (source instanceof BasicBlockStatement) {
      List<Exprent> exprents = source.getExprents();
      if (exprents != null && exprents.size() == 1) {
        // Direct child of CatchStatement/CatchAllStatement (return-only block)
        if (parent instanceof CatchStatement || parent instanceof CatchAllStatement) {
          return true;
        }
      }
      // Catch/try body return: source is in a catch or try body.
      // Preserve catch body returns always. Preserve try body returns
      // only when the catch body also returns (not throws).
      if (exprents != null && !exprents.isEmpty()) {
        Statement catchParent = parent;
        Statement catchChild = source;
        // Walk through SequenceStatements to find CatchStatement
        while (catchParent instanceof SequenceStatement) {
          SequenceStatement seq = (SequenceStatement) catchParent;
          int idx = seq.getStats().getIndexByKey(catchChild.id);
          if (idx < 0 || idx < seq.getStats().size() - 1) break;
          catchChild = catchParent;
          catchParent = catchParent.getParent();
        }
        if (catchParent instanceof CatchStatement || catchParent instanceof CatchAllStatement) {
          if (catchChild != catchParent.getFirst()) {
            // Catch body return - preserve
            return true;
          } else {
            // Try body return - only preserve when the original had return (not goto)
            if (rtfOriginalWasReturn(ex)) {
              return true;
            }
          }
        }
      }
    }

    // Check for IfStatement guard clause pattern
    // Source must be a direct child (ifstat or elsestat) of the IfStatement
    if (!(parent instanceof IfStatement)) return false;
    IfStatement ifStat = (IfStatement) parent;
    if (ifStat.isRtfOriginalHadGotoFallthrough()) return false;
    if (source != ifStat.getIfstat() && source != ifStat.getElsestat()) return false;
    // Only preserve the GUARD return - a BasicBlock whose only content is the
    // void return being stripped. If the body has other code before the return
    // (it's the code body), let the return be stripped normally.
    if (!(source instanceof BasicBlockStatement)) return false;
    List<Exprent> exprents = source.getExprents();
    if (exprents == null || exprents.size() != 1) return false;

    // Match two cases:
    // 1. IFTYPE_IFELSE with rtfBothBranchesTerminate (both branches have returns)
    // 2. IFTYPE_IF where the if-body IS the return (guard clause at method level)
    // Source must be a return-only guard body (ifstat or elsestat) of the IfStatement.
    // This covers: IFTYPE_IF with return as if-body, IFTYPE_IFELSE with return as
    // either body, and cases where reorderIf moved the return to else-body.
    if (source != ifStat.getIfstat() && source != ifStat.getElsestat()) {
      // Already checked above, but defensive
      return false;
    }

    // Skip when nested inside another IfStatement with rtfBothBranchesTerminate
    Statement ancestor = ifStat.getParent();
    while (ancestor != null) {
      if (ancestor instanceof IfStatement) {
        if (((IfStatement) ancestor).isRtfBothBranchesTerminate()) {
          return false;
        }
      }
      ancestor = ancestor.getParent();
    }

    // For non-rtfBothBranchesTerminate cases: skip when the IfStatement has
    // a body AFTER it (it's NOT the last child of its parent). Preserving
    // the return for early-method guards forces javac to place it at the
    // method end, adding a goto to skip over it.
    if (!ifStat.isRtfBothBranchesTerminate()) {
      Statement ifParent = ifStat.getParent();
      if (ifParent instanceof SequenceStatement) {
        SequenceStatement seq = (SequenceStatement) ifParent;
        int idx = seq.getStats().getIndexByKey(ifStat.id);
        if (idx >= 0 && idx < seq.getStats().size() - 1) {
          return false; // not the last child - code follows this guard
        }
      } else if (ifParent instanceof RootStatement) {
        // IfStatement wraps the entire method body - the guard return
        // at method start is better handled by rtfIsGuardClauseAtMethodEnd
        return false;
      }
    }

    return true;
  }


  /**
   * RTF: check if the ExitExprent's bytecode offset corresponds to an actual
   * return instruction in the original bytecode (not a goto that was converted).
   */
  private static boolean rtfOriginalWasReturn(ExitExprent ex) {
    if (ex.bytecode == null) return false;
    MethodWrapper mw = DecompilerContext.getContextProperty(DecompilerContext.CURRENT_METHOD_WRAPPER);
    if (mw == null) return false;
    InstructionSequence seq = mw.methodStruct.getInstructionSequence();
    if (seq == null) return false;

    for (int offset = ex.bytecode.nextSetBit(0); offset >= 0; offset = ex.bytecode.nextSetBit(offset + 1)) {
      int instrIndex = seq.getPointerByAbsOffset(offset);
      if (instrIndex >= 0) {
        Instruction insn = seq.getInstr(instrIndex);
        if (insn.opcode == CodeConstants.opc_return) {
          return true;
        }
      }
    }
    return false;
  }

  // Fixes chars being returned when ints are required
  public static boolean adjustReturnType(RootStatement root, MethodDescriptor desc) {
    boolean res = false;
    // Get all statements with returns
    for (StatEdge retEdge : root.getDummyExit().getAllPredecessorEdges()) {
      Statement ret = retEdge.getSource();

      // Get all exprent in statement
      List<Exprent> exprents = ret.getExprents();
      if (exprents != null && !exprents.isEmpty()) {
        // Get return exprent
        Exprent expr = exprents.get(exprents.size() - 1);
        if (expr instanceof ExitExprent) {
          ExitExprent ex = (ExitExprent) expr;

          List<Exprent> exitExprents = ex.getAllExprents(true);

          // If any of the return expression has constants, adjust them to the return type of the method
          for (Exprent exprent : exitExprents) {
            if (exprent instanceof ConstExprent) {
              ((ConstExprent) exprent).adjustConstType(desc.ret);
              res = true;
            }
          }
        }
      }
    }

    return res;
  }

  // RTF: ensure non-void methods have return statements on all code paths.
  // In RTF mode, IfHelper transformations that restructure if-else blocks into
  // proper return patterns are blocked (to preserve branch direction). This can
  // leave code paths without return statements, causing compilation errors.
  // This pass finds the last statement in the method body and, if it doesn't
  // end with a return/throw, appends a return with the appropriate default value.
  public static boolean ensureMethodReturns(RootStatement root, MethodDescriptor md) {
    if (md.ret == null || md.ret.type == CodeType.VOID) {
      return false;
    }

    Statement body = root.getFirst();
    if (statementEndsWithReturn(body)) {
      return false;
    }

    // The method body does not end with a return on all code paths.
    // Add a return with the default value at the end.
    Exprent defaultValue = createDefaultValue(md.ret);
    ExitExprent exitExpr = new ExitExprent(
        ExitExprent.Type.RETURN, defaultValue, md.ret, null, md);
    Statement lastBlock = findLastAppendableBlock(body);
    if (lastBlock != null && lastBlock.getExprents() != null) {
      lastBlock.getExprents().add(exitExpr);
      return true;
    }

    // If we can't find a suitable block, create a new basic block with the return
    // and append it as a sequence.
    BasicBlockStatement newBlock = BasicBlockStatement.create();
    List<Exprent> exprents = new ArrayList<>();
    exprents.add(exitExpr);
    newBlock.setExprents(exprents);

    if (body instanceof SequenceStatement) {
      body.getStats().addWithKey(newBlock, newBlock.id);
      newBlock.setParent(body);
    } else {
      SequenceStatement seq = new SequenceStatement(Arrays.asList(body, newBlock));
      seq.setAllParent();
      root.replaceStatement(body, seq);
    }
    return true;
  }

  // Check if a statement always ends with a return or throw on all code paths.
  private static boolean statementEndsWithReturn(Statement stat) {
    if (stat == null) {
      return false;
    }

    // Basic block: check if last exprent is a return or throw
    if (stat.getExprents() != null) {
      List<Exprent> exprents = stat.getExprents();
      if (!exprents.isEmpty()) {
        Exprent last = exprents.get(exprents.size() - 1);
        if (last instanceof ExitExprent) {
          return true;
        }
      }
      return false;
    }

    switch (stat.type) {
      case SEQUENCE:
        // Last statement in the sequence must end with return
        List<Statement> seqStats = stat.getStats();
        if (seqStats.isEmpty()) return false;
        return statementEndsWithReturn(seqStats.get(seqStats.size() - 1));

      case IF:
        IfStatement ifStat = (IfStatement) stat;
        if (ifStat.iftype == IfStatement.IFTYPE_IFELSE) {
          // Both branches must end with return
          return statementEndsWithReturn(ifStat.getIfstat())
              && statementEndsWithReturn(ifStat.getElsestat());
        }
        return false;

      case SWITCH:
        SwitchStatement swStat = (SwitchStatement) stat;
        List<Statement> caseStmts = swStat.getCaseStatements();
        if (caseStmts.isEmpty()) return false;
        // Check if all case branches individually end with return
        boolean allReturn = true;
        for (Statement caseStat : caseStmts) {
          if (!statementEndsWithReturn(caseStat)) {
            allReturn = false;
            break;
          }
        }
        if (allReturn) return true;
        // Fall-through: if the last case ends with return and there's a default
        // case, then all earlier non-returning cases fall through to eventually
        // reach the last case's return. This handles unsimplified string-switch
        // patterns where one case just sets a variable and falls through.
        if (statementEndsWithReturn(caseStmts.get(caseStmts.size() - 1))) {
          boolean hasDefault = false;
          for (List<StatEdge> edges : swStat.getCaseEdges()) {
            for (StatEdge edge : edges) {
              if (edge == swStat.getDefaultEdge()) {
                hasDefault = true;
                break;
              }
            }
            if (hasDefault) break;
          }
          if (hasDefault) return true;
        }
        return false;

      case TRY_CATCH:
        // All branches (try body + all catch handlers) must end with return
        for (Statement sub : stat.getStats()) {
          if (!statementEndsWithReturn(sub)) {
            return false;
          }
        }
        return !stat.getStats().isEmpty();

      case CATCH_ALL:
        // For try-finally / try-catch-finally: only the try body (first child)
        // needs all paths returning. The finally handler always runs before the
        // method returns, but doesn't need to itself end with a return.
        // The first child may be a CatchStatement (try-catch-finally) whose
        // own branches (try + catch) are checked recursively.
        return statementEndsWithReturn(stat.getFirst());

      case DO:
        // Infinite loops always "return" in the sense that they don't fall through
        DoStatement doStat = (DoStatement) stat;
        if (doStat.getLooptype() == DoStatement.Type.INFINITE) {
          return true;
        }
        return false;

      case SYNCHRONIZED:
        // Check the body
        SynchronizedStatement synStat = (SynchronizedStatement) stat;
        return statementEndsWithReturn(synStat.getBody());

      default:
        return false;
    }
  }

  // Find the last basic block in the method body where we can append a return.
  private static Statement findLastAppendableBlock(Statement stat) {
    if (stat == null) return null;

    if (stat.getExprents() != null) {
      return stat;
    }

    switch (stat.type) {
      case SEQUENCE:
        List<Statement> seqStats = stat.getStats();
        if (seqStats.isEmpty()) return null;
        return findLastAppendableBlock(seqStats.get(seqStats.size() - 1));

      case IF:
        IfStatement ifStat = (IfStatement) stat;
        // For if-else, we can't just append to the end — both branches need returns.
        // For if-only, append after the if statement.
        if (ifStat.iftype != IfStatement.IFTYPE_IFELSE) {
          return null; // can't append inside an if-only
        }
        return null; // don't append inside if-else either

      default:
        return null;
    }
  }

  // Create a default value expression for the given return type.
  private static Exprent createDefaultValue(VarType retType) {
    // Arrays (including primitive arrays like int[]) are reference types — return null
    if (retType.arrayDim > 0) {
      return new ConstExprent(VarType.VARTYPE_NULL, null, null);
    }
    switch (retType.type) {
      case BOOLEAN:
        return new ConstExprent(VarType.VARTYPE_BOOLEAN, 0, null);
      case BYTE:
      case BYTECHAR:
      case SHORTCHAR:
      case SHORT:
      case CHAR:
      case INT:
        return new ConstExprent(VarType.VARTYPE_INT, 0, null);
      case LONG:
        return new ConstExprent(VarType.VARTYPE_LONG, 0L, null);
      case FLOAT:
        return new ConstExprent(VarType.VARTYPE_FLOAT, 0.0F, null);
      case DOUBLE:
        return new ConstExprent(VarType.VARTYPE_DOUBLE, 0.0, null);
      default:
        // Object types: return null
        return new ConstExprent(VarType.VARTYPE_NULL, null, null);
    }
  }
}