// Copyright 2000-2017 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.modules.decompiler;

import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.modules.decompiler.exps.AssignmentExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.ConstExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.Exprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.FunctionExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.VarExprent;
import org.jetbrains.java.decompiler.modules.decompiler.flow.DirectEdge;
import org.jetbrains.java.decompiler.modules.decompiler.flow.DirectEdgeType;
import org.jetbrains.java.decompiler.modules.decompiler.flow.DirectGraph;
import org.jetbrains.java.decompiler.modules.decompiler.flow.DirectNode;
import org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper;
import org.jetbrains.java.decompiler.modules.decompiler.exps.*;
import org.jetbrains.java.decompiler.modules.decompiler.stats.IfStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.RootStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.Statement;
import org.jetbrains.java.decompiler.modules.decompiler.vars.VarProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair;
import org.jetbrains.java.decompiler.struct.gen.VarType;

import java.util.Deque;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

public class PPandMMHelper {

  private boolean exprentReplaced;
  private VarProcessor varProc;
  private DirectGraph dgraph;

  public PPandMMHelper(VarProcessor varProc) {
    this.varProc = varProc;
  }

  public boolean findPPandMM(RootStatement root) {

    FlattenStatementsHelper flatthelper = new FlattenStatementsHelper();
    this.dgraph = flatthelper.buildDirectGraph(root);

    LinkedList<DirectNode> stack = new LinkedList<>();
    stack.add(this.dgraph.first);

    HashSet<DirectNode> setVisited = new HashSet<>();

    boolean res = false;

    while (!stack.isEmpty()) {

      DirectNode node = stack.removeFirst();

      if (setVisited.contains(node)) {
        continue;
      }
      setVisited.add(node);

      res |= processExprentList(node.exprents);

      for (DirectEdge suc : node.getSuccessors(DirectEdgeType.REGULAR)) {
        stack.add(suc.getDestination());
      }
    }

    return res;
  }

  /**
   * Reconstruct post-increment/decrement expressions from decomposed patterns.
   *
   * Bytecode for post-increment used as an expression (e.g., while(x-- > 0)):
   *   temp = x; x = x - 1; ...use temp...
   *
   * After findPPandMM converts x = x - 1 to --x (MMI), we have:
   *   temp = x; --x; ...use temp...
   *
   * This method detects that pattern and converts it to:
   *   temp = x--; ...use temp...
   *
   * The assignment temp = x-- can then be further inlined by StackVarsProcessor.
   * Only applies in RTF mode.
   */
  public boolean reconstructPostIncrement(RootStatement root) {
    if (!DecompilerContext.isRoundtripFidelity()) {
      return false;
    }

    FlattenStatementsHelper flatthelper = new FlattenStatementsHelper();
    DirectGraph graph = flatthelper.buildDirectGraph(root);

    LinkedList<DirectNode> stack = new LinkedList<>();
    stack.add(graph.first);

    Set<DirectNode> setVisited = new HashSet<>();
    boolean res = false;

    while (!stack.isEmpty()) {
      DirectNode node = stack.removeFirst();

      if (setVisited.contains(node)) {
        continue;
      }
      setVisited.add(node);

      res |= reconstructPostIncrementInList(node.exprents);

      for (DirectEdge suc : node.getSuccessors(DirectEdgeType.REGULAR)) {
        stack.add(suc.getDestination());
      }
    }

    return res;
  }

  /**
   * Within a single exprent list, find consecutive pairs:
   *   [i]   temp = var          (assignment: VarExprent = VarExprent)
   *   [i+1] ++var or --var      (PPI or MMI, operand matches var)
   *
   * Transform to:
   *   [i]   temp = var++ or temp = var--   (IPP or IMM as expression)
   *   Remove [i+1]
   */
  private boolean reconstructPostIncrementInList(List<Exprent> lst) {
    boolean result = false;

    for (int i = 0; i < lst.size() - 1; i++) {
      Exprent first = lst.get(i);
      Exprent second = lst.get(i + 1);

      // Second must be PPI (++var) or MMI (--var)
      if (!(second instanceof FunctionExprent)) {
        continue;
      }
      FunctionExprent ppFunc = (FunctionExprent) second;
      if (ppFunc.getFuncType() != FunctionExprent.FunctionType.PPI
          && ppFunc.getFuncType() != FunctionExprent.FunctionType.MMI) {
        continue;
      }

      Exprent ppOperand = ppFunc.getLstOperands().get(0);
      if (!(ppOperand instanceof VarExprent)) {
        continue;
      }
      VarExprent ppVar = (VarExprent) ppOperand;

      // First must be an assignment: temp = var
      if (!(first instanceof AssignmentExprent)) {
        continue;
      }
      AssignmentExprent assign = (AssignmentExprent) first;
      if (assign.getCondType() != null) {
        continue;
      }
      if (!(assign.getLeft() instanceof VarExprent)) {
        continue;
      }
      if (!(assign.getRight() instanceof VarExprent)) {
        continue;
      }

      VarExprent tempVar = (VarExprent) assign.getLeft();
      VarExprent savedVar = (VarExprent) assign.getRight();

      // The saved var and the PPI operand must refer to the same original variable
      if (!varsEqual(savedVar, ppVar)) {
        continue;
      }

      // Convert PPI to IPP (post-increment) or MMI to IMM (post-decrement)
      FunctionExprent.FunctionType postType =
          ppFunc.getFuncType() == FunctionExprent.FunctionType.PPI
              ? FunctionExprent.FunctionType.IPP
              : FunctionExprent.FunctionType.IMM;

      FunctionExprent postIncrement = new FunctionExprent(postType, ppVar, ppFunc.bytecode);
      postIncrement.setImplicitType(ppFunc.getExprType());

      // Replace the assignment's right side with the post-increment
      assign.setRight(postIncrement);
      postIncrement.addBytecodeOffsets(savedVar.bytecode);

      // Remove the standalone PPI/MMI
      lst.remove(i + 1);

      result = true;
      // Don't decrement i - we've removed the next element, so i now points to
      // whatever was after the PPI, and we should check the new pair
    }

    return result;
  }

  private boolean processExprentList(List<Exprent> lst) {

    boolean result = false;

    for (int i = 0; i < lst.size(); i++) {
      Exprent exprent = lst.get(i);
      exprentReplaced = false;

      Exprent retexpr = processExprentRecursive(exprent);
      if (retexpr != null) {
        lst.set(i, retexpr);

        result = true;
        i--; // process the same exprent again
      }

      result |= exprentReplaced;
    }

    return result;
  }

  private Exprent processExprentRecursive(Exprent exprent) {

    boolean replaced = true;
    while (replaced) {
      replaced = false;

      for (Exprent expr : exprent.getAllExprents()) {
        Exprent retexpr = processExprentRecursive(expr);
        if (retexpr != null) {
          exprent.replaceExprent(expr, retexpr);
          retexpr.addBytecodeOffsets(expr.bytecode);
          replaced = true;
          exprentReplaced = true;
          break;
        }
      }
    }

    if (exprent instanceof AssignmentExprent) {
      AssignmentExprent as = (AssignmentExprent)exprent;

      if (as.getRight() instanceof FunctionExprent) {
        FunctionExprent func = (FunctionExprent)as.getRight();

        VarType midlayer = func.getFuncType().castType;
        if (midlayer != null) {
          if (func.getLstOperands().get(0) instanceof FunctionExprent) {
            func = (FunctionExprent)func.getLstOperands().get(0);
          }
          else {
            return null;
          }
        }

        if (func.getFuncType() == FunctionExprent.FunctionType.ADD ||
            func.getFuncType() == FunctionExprent.FunctionType.SUB) {
          Exprent econd = func.getLstOperands().get(0);
          Exprent econst = func.getLstOperands().get(1);

          if (!(econst instanceof ConstExprent) && econd instanceof ConstExprent &&
              func.getFuncType() == FunctionExprent.FunctionType.ADD) {
            econd = econst;
            econst = func.getLstOperands().get(0);
          }

          if (econst instanceof ConstExprent && ((ConstExprent)econst).hasValueOne()) {
            Exprent left = as.getLeft();

            VarType condtype = left.getExprType();
            if (exprsEqual(left, econd) && (midlayer == null || midlayer.equals(condtype))) {
              FunctionExprent ret = new FunctionExprent(
                func.getFuncType() == FunctionExprent.FunctionType.ADD ? FunctionExprent.FunctionType.PPI : FunctionExprent.FunctionType.MMI,
                econd, func.bytecode);
              ret.setImplicitType(condtype);

              exprentReplaced = true;

              if (!left.equals(econd)) {
                updateVersions(this.dgraph, new VarVersionPair((VarExprent)left), new VarVersionPair((VarExprent)econd));
              }

              return ret;
            }
          }
        }
      }
    }

    return null;
  }

  private boolean exprsEqual(Exprent e1, Exprent e2) {
    if (e1 == e2) return true;
    if (e1 == null || e2 == null) return false;
    if (e1 instanceof VarExprent) {
      return varsEqual(e1, e2);
    }
    return e1.equals(e2);
  }

  private boolean varsEqual(Exprent e1, Exprent e2) {
    if (!(e1 instanceof VarExprent)) return false;
    if (!(e2 instanceof VarExprent)) return false;

    VarExprent v1 = (VarExprent)e1;
    VarExprent v2 = (VarExprent)e2;
    return varProc.getVarOriginalIndex(v1.getIndex()) == varProc.getVarOriginalIndex(v2.getIndex());
    // TODO: Verify the types are in the same 'family' {byte->short->int}
    //        && InterpreterUtil.equalObjects(v1.getVarType(), v2.getVarType());
  }


  private void updateVersions(DirectGraph graph, final VarVersionPair oldVVP, final VarVersionPair newVVP) {
    graph.iterateExprents(new DirectGraph.ExprentIterator() {
      @Override
      public int processExprent(Exprent exprent) {
        List<Exprent> lst = exprent.getAllExprents(true);
        lst.add(exprent);

        for (Exprent expr : lst) {
          if (expr instanceof VarExprent) {
            VarExprent var = (VarExprent)expr;
            if (var.getIndex() == oldVVP.var && var.getVersion() == oldVVP.version) {
              var.setIndex(newVVP.var);
              var.setVersion(newVVP.version);
            }
          }
        }

        return 0;
      }
    });
  }

  //
  // ++a
  // (a > 0) {
  //   ...
  // }
  //
  // becomes
  //
  // if (++a > 0) {
  //   ...
  // }
  //
  // Semantically the same, but cleaner and allows for loop inlining
  public static boolean inlinePPIandMMIIf(RootStatement stat) {
    boolean res = inlinePPIandMMIIfRec(stat);

    if (res) {
      SequenceHelper.condenseSequences(stat);
    }

    return res;
  }

  private static boolean inlinePPIandMMIIfRec(Statement stat) {
    boolean res = false;
    for (Statement st : stat.getStats()) {
      res |= inlinePPIandMMIIfRec(st);
    }

    if (stat.getExprents() != null && !stat.getExprents().isEmpty()) {
      IfStatement destination = findIfSuccessor(stat);

      if (destination != null) {
        // RTF: handle "copy = field++; if (... copy ...) {}" pattern.
        // The last exprent is an assignment where the RHS is a post-increment on a field.
        // The copy variable is used in the if-condition (e.g., as an array index).
        // Inline the post-increment into the if-condition, eliminating the copy variable.
        Exprent lastExpr = stat.getExprents().get(stat.getExprents().size() - 1);
        if (lastExpr instanceof AssignmentExprent assignExpr
            && assignExpr.getLeft() instanceof VarExprent copyVar
            && assignExpr.getRight() instanceof FunctionExprent funcExpr
            && (funcExpr.getFuncType() == FunctionExprent.FunctionType.IPP
                || funcExpr.getFuncType() == FunctionExprent.FunctionType.IMM)) {
          Exprent ifExpr = destination.getHeadexprent().getCondition();
          // Find and replace the copy variable in the if-condition
          VarExprent found = findSingleVarUse(ifExpr, copyVar);
          if (found != null) {
            replaceExprentInTree(ifExpr, found, funcExpr);
            funcExpr.addBytecodeOffsets(found.bytecode);
            stat.getExprents().remove(lastExpr);
            destination.setHasPPMM(true);
            res = true;
          }
        }

        // Last exprent: inline standalone PPI/MMI (++var/--var) into if-condition.
        // RTF: skip this - inlining moves the iinc instruction from BEFORE the
        // if-condition to INSIDE argument evaluation, changing bytecode order.
        if (DecompilerContext.isRoundtripFidelity()) {
          return res;
        }
        Exprent expr = stat.getExprents().isEmpty() ? null : stat.getExprents().get(stat.getExprents().size() - 1);
        if (expr instanceof FunctionExprent) {
          FunctionExprent func = (FunctionExprent)expr;

          if (func.getFuncType() == FunctionExprent.FunctionType.PPI || func.getFuncType() == FunctionExprent.FunctionType.MMI) {
            Exprent inner = func.getLstOperands().get(0);

            if (inner instanceof VarExprent) {
              Exprent ifExpr = destination.getHeadexprent().getCondition();

              if (ifExpr instanceof FunctionExprent) {
                FunctionExprent ifFunc = (FunctionExprent)ifExpr;

                while (ifFunc.getFuncType() == FunctionExprent.FunctionType.BOOL_NOT) {
                  Exprent innerFunc = ifFunc.getLstOperands().get(0);

                  if (innerFunc instanceof FunctionExprent) {
                    ifFunc = (FunctionExprent)innerFunc;
                  } else {
                    break;
                  }
                }

                // Search for usages of variable
                boolean found = false;
                VarExprent old = null;
                for (Exprent ex : ifFunc.getAllExprents(true)) {
                  if (ex instanceof VarExprent) {
                    VarExprent var = (VarExprent)ex;
                    if (var.getIndex() == ((VarExprent)inner).getIndex()) {
                      // Found variable to replace

                      // Fail if we've already seen this variable!
                      if (found) {
                        return false;
                      }

                      // Store the var we want to replace
                      old = var;
                      found = true;
                    }
                  } else if (ex instanceof FunctionExprent) {
                    FunctionExprent funcEx = (FunctionExprent)ex;

                    if (funcEx.getFuncType() == FunctionExprent.FunctionType.BOOLEAN_AND || funcEx.getFuncType() == FunctionExprent.FunctionType.BOOLEAN_OR) {
                      // Cannot yet handle these as we aren't able to decompose a condition into parts that are always run (not short-circuited) and parts that are
                      // FIXME: handle this case
                      return false;
                    }
                  }
                }

                if (found) {
                  Deque<Exprent> stack = new LinkedList<>();
                  stack.push(ifFunc);

                  while (!stack.isEmpty()) {
                    Exprent exprent = stack.pop();

                    for (Exprent ex : exprent.getAllExprents()) {
                      if (ex == old) {
                        // Replace variable with ppi/mmi
                        exprent.replaceExprent(old, expr);
                        expr.addBytecodeOffsets(old.bytecode);

                        // No more itr
                        stack.clear();
                        break;
                      }

                      stack.push(ex);
                    }
                  }

                  // Remove old expr
                  stat.getExprents().remove(expr);
                  res = true;

                  destination.setHasPPMM(true);
                }
              }
            }
          }
        }
      }
    }

    return res;
  }

  /** Find a single use of a variable in an expression tree. Returns null if zero or multiple uses. */
  private static VarExprent findSingleVarUse(Exprent expr, VarExprent target) {
    VarExprent found = null;
    for (Exprent sub : expr.getAllExprents(true)) {
      if (sub instanceof VarExprent ve
          && ve.getIndex() == target.getIndex()
          && ve.getVersion() == target.getVersion()) {
        if (found != null) return null; // multiple uses
        found = ve;
      }
    }
    // Check the expression itself
    if (expr instanceof VarExprent ve
        && ve.getIndex() == target.getIndex()
        && ve.getVersion() == target.getVersion()) {
      if (found != null) return null;
      found = ve;
    }
    return found;
  }

  /** Replace an exprent in an expression tree. */
  private static void replaceExprentInTree(Exprent root, Exprent old, Exprent replacement) {
    Deque<Exprent> stack = new LinkedList<>();
    stack.push(root);
    while (!stack.isEmpty()) {
      Exprent current = stack.pop();
      for (Exprent sub : current.getAllExprents()) {
        if (sub == old) {
          current.replaceExprent(old, replacement);
          return;
        }
        stack.push(sub);
      }
    }
  }

  private static IfStatement findIfSuccessor(Statement stat) {
    if (stat.getParent() instanceof IfStatement) {
      if (stat.getParent().getFirst() == stat) {
        return (IfStatement) stat.getParent();
      }
    }

    return null;
  }
}
