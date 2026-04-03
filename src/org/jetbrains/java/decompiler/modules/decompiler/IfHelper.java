// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.modules.decompiler;

import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.extern.IFernflowerPreferences;
import org.jetbrains.java.decompiler.modules.decompiler.IfNode.EdgeType;
import org.jetbrains.java.decompiler.modules.decompiler.exps.ConstExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.ExitExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.Exprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.FunctionExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.InvocationExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.FunctionExprent.FunctionType;
import org.jetbrains.java.decompiler.modules.decompiler.exps.IfExprent;
import org.jetbrains.java.decompiler.code.cfg.BasicBlock;
import org.jetbrains.java.decompiler.modules.decompiler.stats.BasicBlockStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.IfStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.RootStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.SequenceStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.Statement;

import java.util.*;

public final class IfHelper {
  public static boolean mergeAllIfs(RootStatement root) {
    boolean res = mergeAllIfsRec(root, new HashSet<>());
    if (res) {
      SequenceHelper.condenseSequences(root);
    }
    return res;
  }

  private static boolean mergeAllIfsRec(Statement stat, Set<? super Integer> setReorderedIfs) {
    boolean res = false;

    if (stat.getExprents() == null) {
      while (true) {
        boolean changed = false;

        for (Statement st : stat.getStats()) {
          res |= mergeAllIfsRec(st, setReorderedIfs);

          // collapse composed if's
          if (mergeIfs(st, setReorderedIfs)) {
            changed = true;
            break;
          }
        }

        res |= changed;

        if (!changed) {
          break;
        }
      }
    }

    return res;
  }

  public static boolean mergeIfs(Statement statement, Set<? super Integer> setReorderedIfs) {
    if (!(statement instanceof IfStatement) && !(statement instanceof SequenceStatement)) {
      return false;
    }

    boolean res = false;

    loop:
    while (true) {
      List<Statement> lst = new ArrayList<>();
      if (statement instanceof IfStatement) {
        lst.add(statement);
      } else {
        lst.addAll(statement.getStats());
      }

      boolean stsingle = (lst.size() == 1);

      for (Statement stat : lst) {
        if (stat instanceof IfStatement) {
          IfNode rtnode = IfNode.build((IfStatement) stat, stsingle);

          if (collapseIfIf(rtnode)) {
            res = true;
            ValidationHelper.validateStatement(stat.getTopParent());
            continue loop;
          }

          if (!setReorderedIfs.contains(stat.id)) {
            if (collapseIfElse(rtnode)) {
              res = true;
              ValidationHelper.validateStatement(stat.getTopParent());
              continue loop;
            }

            if (collapseElse(rtnode)) {
              res = true;
              ValidationHelper.validateStatement(stat.getTopParent());
              continue loop;
            }

            if (DecompilerContext.getOption(IFernflowerPreferences.TERNARY_CONDITIONS) && collapseTernary(rtnode)) {
              res = true;
              ValidationHelper.validateStatement(stat.getTopParent());
              continue loop;
            }

            // TODO: This should maybe be moved (probably to reorderIf)
            if (ifElseChainDenesting(rtnode)) {
              res = true;
              ValidationHelper.validateStatement(stat.getTopParent());
              continue loop;
            }
          }

          if (reorderIf((IfStatement) stat)) {
            res = true;
            ValidationHelper.validateStatement(stat.getTopParent());
            setReorderedIfs.add(stat.id);
            continue loop;
          }
        }
      }

      return res;
    }
  }

  // if-if branch (&& operation)
  // if (cond1) {
  //   if (cond2) {
  //     A // or goto A
  //   }
  //   goto B
  // }
  // B // or goto B
  // into
  // if (cond1 && cond2) {
  //   A // or goto A
  // }
  // B // or goto B
  private static boolean collapseIfIf(IfNode rtnode) {
    if (rtnode.innerType == EdgeType.DIRECT) {
      IfNode ifbranch = rtnode.innerNode;
      if (ifbranch.innerNode != null) { // make sure that ifBranch is an ifStatement
        if (rtnode.successorNode.value == ifbranch.successorNode.value) {

          IfStatement ifparent = (IfStatement) rtnode.value;
          IfStatement ifchild = (IfStatement) ifbranch.value;
          Statement ifinner = ifbranch.innerNode.value;

          // RTF: don't merge nested ifs when the parent has the goto-fallthrough
          // flag. Merging converts ifXX+goto (2-instruction) into a single
          // reversed ifYY, changing the bytecode opcode and instruction count.
          if (DecompilerContext.isRoundtripFidelity() && ifparent.isRtfOriginalHadGotoFallthrough()) {
            return false;
          }

          if (ifchild.getFirst().getExprents().isEmpty() && !ifchild.hasPPMM()) {

            ifparent.getIfEdge().remove();
            ifchild.getFirstSuccessor().remove();
            ifparent.getStats().removeWithKey(ifchild.id);

            if (ifbranch.innerType == EdgeType.INDIRECT) { // inner code is remote (goto B case)
              ifparent.setIfstat(null);

              StatEdge ifedge = ifchild.getIfEdge();

              ifedge.changeSource(ifparent.getFirst());

              if (ifedge.closure == ifchild) {
                ifedge.closure = null;
              }

              ifparent.setIfEdge(ifedge);
            } else { // inner code is actually code (B case)
              ifchild.getIfEdge().remove();

              StatEdge ifedge = new StatEdge(StatEdge.TYPE_REGULAR, ifparent.getFirst(), ifinner);
              ifparent.getFirst().addSuccessor(ifedge);
              ifparent.setIfEdge(ifedge);
              ifparent.setIfstat(ifinner);

              ifparent.getStats().addWithKey(ifinner, ifinner.id);
              ifinner.setParent(ifparent);

              if (ifinner.hasAnySuccessor()) {
                StatEdge edge = ifinner.getFirstSuccessor();
                if (edge.closure == ifchild) {
                  edge.closure = ifparent;
                }
              }
            }

            // merge if conditions
            IfExprent statexpr = ifparent.getHeadexprent();

            List<Exprent> lstOperands = new ArrayList<>();
            lstOperands.add(statexpr.getCondition());
            lstOperands.add(ifchild.getHeadexprent().getCondition());

            statexpr.setCondition(new FunctionExprent(FunctionType.BOOLEAN_AND, lstOperands, null));
            statexpr.addBytecodeOffsets(ifchild.getHeadexprent().bytecode);

            // RTF: propagate flags from child to parent.
            // The child's head block may have had a goto/return fall-through that
            // should prevent this compound condition from being merged into ||.
            if (ifchild.getFirst() instanceof BasicBlockStatement && ifparent.getFirst() instanceof BasicBlockStatement) {
              BasicBlock childBlock = ((BasicBlockStatement) ifchild.getFirst()).getBlock();
              BasicBlock parentBlock = ((BasicBlockStatement) ifparent.getFirst()).getBlock();
              if (childBlock.rtfFallthroughWasGoto) {
                parentBlock.rtfFallthroughWasGoto = true;
              }
              if (childBlock.rtfFallthroughWasReturn) {
                parentBlock.rtfFallthroughWasReturn = true;
              }
            }

            return true;
          }
        }
      }
    }

    return false;
  }

  // if-else branch
  // if (cond1) {
  //   if (cond2) {
  //     goto A
  //   }
  //   goto B
  // }
  // A // or goto A
  // into
  // if (cond1 && !cond2) {
  //   goto B
  // }
  // A // or goto A
  private static boolean collapseIfElse(IfNode rtnode) {
    if (rtnode.innerType == EdgeType.DIRECT) {
      IfNode ifbranch = rtnode.innerNode;
      if (ifbranch.innerNode != null) { // make sure that ifBranch is an ifStatement
        if (rtnode.successorNode.value == ifbranch.innerNode.value) {

          IfStatement ifparent = (IfStatement) rtnode.value;
          IfStatement ifchild = (IfStatement) ifbranch.value;

          if (ifchild.getFirst().getExprents().isEmpty()) {

            ifparent.getIfEdge().remove();
            ifchild.getIfEdge().remove();
            ifparent.getStats().removeWithKey(ifchild.id);

            // if (cond1) {
            //   if (cond2) {
            //     goto A
            //   }
            //   goto B
            // }
            // A // or goto A

            ifparent.setIfstat(null);

            StatEdge ifedge = ifchild.getFirstSuccessor();
            ifedge.changeSource(ifparent.getFirst());
            ifparent.setIfEdge(ifedge);

            // merge if conditions
            IfExprent statexpr = ifparent.getHeadexprent();

            List<Exprent> lstOperands = new ArrayList<>();
            lstOperands.add(statexpr.getCondition());
            lstOperands.add(new FunctionExprent(FunctionType.BOOL_NOT, ifchild.getHeadexprent().getCondition(), null));
            statexpr.setCondition(new FunctionExprent(FunctionType.BOOLEAN_AND, lstOperands, null));
            statexpr.addBytecodeOffsets(ifchild.getHeadexprent().bytecode);

            return true;
          }
        }
      }
    }

    return false;
  }

  /**
   * Check if an if-body's last BasicBlock had a trailing goto in the original bytecode.
   * Walks to the last BasicBlockStatement in the body and checks rtfHadTrailingGoto.
   */
  private static boolean rtfIfBodyHadTrailingGoto(Statement body) {
    // Find the last BasicBlockStatement in the body
    Statement last = body;
    while (!last.getStats().isEmpty()) {
      last = last.getStats().get(last.getStats().size() - 1);
    }
    if (last instanceof BasicBlockStatement) {
      return ((BasicBlockStatement) last).getBlock().rtfHadTrailingGoto;
    }
    return false;
  }

  /**
   * Checks whether an if-statement's if-body is a guard clause (terminates via return or throw).
   * A guard clause is a simple block whose last exprent is an ExitExprent (return/throw),
   * or whose if-edge is a break/continue. In RTF mode, these should be preserved as-is
   * rather than being merged or swapped into if-else blocks.
   */
  private static boolean isRtfGuardClause(IfStatement ifstat) {
    if (!DecompilerContext.isRoundtripFidelity()) {
      return false;
    }

    // Only applies to simple if (no else)
    if (ifstat.iftype == IfStatement.IFTYPE_IFELSE) {
      return false;
    }

    // Skip null-check-then-close patterns used by try-with-resources.
    // These must remain mergeable so TryWithResourcesProcessor can recognize them.
    if (isNullCheckClosePattern(ifstat)) {
      return false;
    }

    Statement ifbody = ifstat.getIfstat();
    if (ifbody != null) {
      // If-body is an inline statement - check if it ends with return/throw
      if (ifbody instanceof BasicBlockStatement) {
        List<Exprent> exprents = ifbody.getExprents();
        if (exprents != null && !exprents.isEmpty()) {
          Exprent last = exprents.get(exprents.size() - 1);
          if (last instanceof ExitExprent) {
            return true;
          }
        }
      }
      return false;
    }

    // If-body is null (goto-style), check the if-edge type
    StatEdge ifedge = ifstat.getIfEdge();
    if (ifedge != null) {
      int edgeType = ifedge.getType();
      if (edgeType == StatEdge.TYPE_BREAK || edgeType == StatEdge.TYPE_CONTINUE) {
        return true;
      }
    }

    return false;
  }

  /**
   * Detect null-check-then-close patterns from try-with-resources:
   * if (resource != null) { resource.close(); }
   */
  private static boolean isNullCheckClosePattern(IfStatement ifstat) {
    // Check if the condition is a null check (ifnull/ifnonnull)
    Exprent headExpr = ifstat.getHeadexprent();
    if (!(headExpr instanceof IfExprent)) {
      return false;
    }
    IfExprent ifExpr = (IfExprent) headExpr;
    Exprent cond = ifExpr.getCondition();

    // Must be a null comparison: var != null or var == null
    boolean isNullCheck = false;
    if (cond instanceof FunctionExprent) {
      FunctionExprent func = (FunctionExprent) cond;
      FunctionType ftype = func.getFuncType();
      if (ftype == FunctionType.EQ || ftype == FunctionType.NE) {
        List<Exprent> operands = func.getLstOperands();
        if (operands.size() == 2) {
          isNullCheck = (operands.get(0) instanceof ConstExprent && ((ConstExprent) operands.get(0)).getValue() == null)
              || (operands.get(1) instanceof ConstExprent && ((ConstExprent) operands.get(1)).getValue() == null);
        }
      }
    }
    if (!isNullCheck) {
      return false;
    }

    // Check if the body or a nearby sibling contains a .close() call
    Statement ifbody = ifstat.getIfstat();
    if (containsCloseCall(ifbody)) {
      return true;
    }

    // When if-body is null (goto-style), check the next sibling in parent sequence
    Statement parent = ifstat.getParent();
    if (parent instanceof SequenceStatement) {
      List<Statement> stats = parent.getStats();
      for (int i = 0; i < stats.size() - 1; i++) {
        if (stats.get(i) == ifstat) {
          if (containsCloseCall(stats.get(i + 1))) {
            return true;
          }
          break;
        }
      }
    }

    return false;
  }

  private static boolean containsCloseCall(Statement stat) {
    if (stat == null) {
      return false;
    }
    if (stat instanceof BasicBlockStatement) {
      List<Exprent> exprents = stat.getExprents();
      if (exprents != null) {
        for (Exprent expr : exprents) {
          if (expr instanceof InvocationExprent) {
            if ("close".equals(((InvocationExprent) expr).getName())) {
              return true;
            }
          }
        }
      }
    }
    // Check first child for sequences
    if (!stat.getStats().isEmpty()) {
      return containsCloseCall(stat.getStats().get(0));
    }
    return false;
  }

  private static boolean collapseElse(IfNode rtnode) {
    if (rtnode.successorType == EdgeType.DIRECT) {
      IfNode elsebranch = rtnode.successorNode;
      if (elsebranch.innerNode != null) { // make sure that elseBranch is an ifStatement

        int path = elsebranch.successorNode.value == rtnode.innerNode.value ? 2 :
          (elsebranch.innerNode.value == rtnode.innerNode.value ? 1 : 0);

        if (path > 0) {
          // path == 1
          // if (cond1) {
          //   goto A
          // }
          // if (cond2) {
          //   goto A
          // } else {
          //   // inner code
          // }
          // into
          // if (cond1 || cond2) {
          //   goto A
          // } else {
          //   // inner code
          // }

          // path == 2
          // if (cond1) {
          //   goto A
          // }
          // if (cond2) {
          //   // inner code
          // }
          // A // or goto A
          // into
          // if (!cond1 && cond2) {
          //   // inner code
          // }
          // A // or goto A

          IfStatement firstif = (IfStatement) rtnode.value;

          // RTF: path 2 wraps the first condition in BOOL_NOT, which inverts the
          // branch opcode polarity. The per-IfStatement rtfConditionFlipped flag
          // cannot represent sub-expression polarity in the merged compound condition.
          // Block the merge to preserve the original branch directions.
          if (path == 2 && DecompilerContext.isRoundtripFidelity()) {
            return false;
          }
          // RTF: path 1 merges sequential ifs into ||. Block when the original
          // had SEPARATE if-statements (ifeq+goto per term) - detected by the
          // rtfFallthroughWasGoto flag set during CFG processing.
          if (path == 1 && DecompilerContext.isRoundtripFidelity()) {
            Statement head = firstif.getFirst();
            if (head instanceof BasicBlockStatement) {
              if (((BasicBlockStatement) head).getBlock().rtfFallthroughWasGoto) {
                return false;
              }
            }
          }
          IfStatement secondif = (IfStatement) elsebranch.value;
          Statement parent = firstif.getParent();

          if (secondif.getFirst().getExprents().isEmpty()) {

            firstif.getIfEdge().remove();

            // remove first if
            firstif.removeAllSuccessors(secondif);

            for (StatEdge edge : firstif.getAllPredecessorEdges()) {
              if (!firstif.containsStatementStrict(edge.getSource())) {
                // TODO: why is this check here? If this check were to fail, this if
                //  should have been a loop instead of an if statement.
                edge.changeDestination(secondif);
              }
            }

            parent.getStats().removeWithKey(firstif.id);
            if (parent.getFirst() == firstif) {
              parent.setFirst(secondif);
            }

            // merge if conditions
            IfExprent statexpr = secondif.getHeadexprent();

            List<Exprent> lstOperands = new ArrayList<>();
            lstOperands.add(firstif.getHeadexprent().getCondition());

            if (path == 2) {
              lstOperands.set(0, new FunctionExprent(FunctionType.BOOL_NOT, lstOperands.get(0), null));
            }

            lstOperands.add(statexpr.getCondition());

            statexpr
              .setCondition(new FunctionExprent(path == 1 ? FunctionType.BOOLEAN_OR : FunctionType.BOOLEAN_AND, lstOperands, null));

            if (secondif.getFirst().getExprents().isEmpty() && // second is guranteed to be empty already
                !firstif.getFirst().getExprents().isEmpty()) {

              secondif.replaceStatement(secondif.getFirst(), firstif.getFirst());
            }

            return true;
          }
        }
      } else if (elsebranch.successorNode != null) { // else branch is not an if statement, but is direct
        if (elsebranch.successorNode.value == rtnode.innerNode.value) {
          // if (cond1) {
          //   goto A
          // }
          // B
          // goto A;
          //
          // into
          //
          // if (!cond1) {
          //   B
          // }
          // goto A;

          IfStatement firstif = (IfStatement) rtnode.value;

          // RTF: preserve guard clauses - don't absorb the next statement into
          // a negated if-body when the original if-body terminates (return/throw)
          if (isRtfGuardClause(firstif)) {
            return false;
          }

          Statement second = elsebranch.value;

          firstif.removeAllSuccessors(second);

          for (StatEdge edge : second.getAllSuccessorEdges()) {
            edge.changeSource(firstif);
          }

          StatEdge ifedge = firstif.getIfEdge();
          ifedge.remove();

          second.addSuccessor(new StatEdge(ifedge.getType(), second, ifedge.getDestination(), ifedge.closure));

          StatEdge newifedge = new StatEdge(StatEdge.TYPE_REGULAR, firstif.getFirst(), second);
          firstif.getFirst().addSuccessor(newifedge);
          firstif.setIfEdge(newifedge);
          firstif.setIfstat(second);
          firstif.toggleRtfIfBodyIsFallThrough(); // body semantics changed

          firstif.getStats().addWithKey(second, second.id);
          second.setParent(firstif);

          firstif.getParent().getStats().removeWithKey(second.id);

          // negate the if condition
          IfExprent statexpr = firstif.getHeadexprent();
          statexpr
            .setCondition(new FunctionExprent(FunctionType.BOOL_NOT, statexpr.getCondition(), null));

          // RTF: track that this transformation flipped the condition direction
          if (DecompilerContext.isRoundtripFidelity()) {
            firstif.toggleRtfConditionFlipped();
          }

          return true;
        }
      }
    }
    return false;
  }

  // convert
  // if (cond1) {
  //   if (cond2) {
  //     goto A
  //   }
  //   goto B
  // } else {
  //   if (cond3) {
  //     goto A
  //   }
  //   goto B
  // }
  //
  // into
  // if (cond1 ? cond2 : cond3) {
  //   goto A
  // }
  // goto B

  // if goto A and goto B are swapped in `if (cond2)`, then cond2 is negated
  private static boolean collapseTernary(IfNode rtnode) {
    if (rtnode.innerType == EdgeType.DIRECT && rtnode.successorType == EdgeType.ELSE) {
      // if (cond1) {
      //   if (cond2) {
      //     goto A
      //   }
      //   goto B
      // } else {
      //   if (cond3) {
      //     goto A
      //   }
      //   goto B
      // }
      IfNode ifBranch = rtnode.innerNode;
      IfNode elseBranch = rtnode.successorNode;

      if (ifBranch.innerType == EdgeType.INDIRECT && ifBranch.successorType == EdgeType.INDIRECT &&
          elseBranch.innerType == EdgeType.INDIRECT && elseBranch.successorType == EdgeType.INDIRECT &&
          ifBranch.value.getFirst().getExprents().isEmpty() && elseBranch.value.getFirst().getExprents().isEmpty()) {

        boolean inverted;
        if (ifBranch.innerNode.value == elseBranch.innerNode.value &&
            ifBranch.successorNode.value == elseBranch.successorNode.value) {
          inverted = false;
        } else if (ifBranch.innerNode.value == elseBranch.successorNode.value &&
                   ifBranch.successorNode.value == elseBranch.innerNode.value) {
          inverted = true;
        } else {
          return false;
        }

        IfStatement mainIf = (IfStatement) rtnode.value;
        IfStatement firstIf = (IfStatement) ifBranch.value;
        IfStatement secondIf = (IfStatement) elseBranch.value;

        // remove first if
        mainIf.getStats().removeWithKey(firstIf.id);
        mainIf.getIfEdge().remove();
        mainIf.setIfstat(null);

        // remove second if
        mainIf.getStats().removeWithKey(secondIf.id);
        mainIf.getElseEdge().remove();
        mainIf.setElsestat(null);

        // remove unused first if's edges
        firstIf.getIfEdge().remove();
        firstIf.getFirstSuccessor().remove();

        // move second if jump to main if
        mainIf.setIfEdge(secondIf.getIfEdge());
        mainIf.getIfEdge().changeSource(mainIf.getFirst());

        // remove (weird?) if else successor, produced by dom parsing
        // TODO: remove when dom parsing is fixed
        if (mainIf.hasAnySuccessor()) {
          mainIf.getFirstSuccessor().remove();
        }

        // move seconds successor to be the if's successor
        secondIf.getFirstSuccessor().changeSource(mainIf);
        if (mainIf.getFirstSuccessor().closure == mainIf) {
          // TODO: always removing causes some <unknownclosure> bugs, while not removing causes issues with invalid closure validations
          if (mainIf.getFirstSuccessor().getSource() != mainIf) {
            mainIf.getFirstSuccessor().removeClosure();
          }

          mainIf.getFirstSuccessor().changeType(StatEdge.TYPE_REGULAR);
        }

        // mark the if as an if and not an if else
        mainIf.iftype = IfStatement.IFTYPE_IF;
        mainIf.setElseEdge(null);

        // merge if conditions
        IfExprent statexpr = mainIf.getHeadexprent();

        List<Exprent> lstOperands = new ArrayList<>();
        lstOperands.add(mainIf.getHeadexprent().getCondition());
        lstOperands.add(firstIf.getHeadexprent().getCondition());

        if (inverted) {
          lstOperands.set(1, new FunctionExprent(FunctionType.BOOL_NOT, lstOperands.get(1), null));
        }

        lstOperands.add(secondIf.getHeadexprent().getCondition());

        statexpr.setCondition(new FunctionExprent(FunctionType.TERNARY, lstOperands, null));
        return true;
      }
    }

    return false;
  }


  // Convert
  //
  // if (condA) {
  //   if (condB) {
  //     X
  //   } else {
  //     Y
  //   }
  //   goto end
  // }
  // Z
  // end
  //
  // To
  //
  // if (!condA) {
  //   Z
  // }
  // else {
  //   if (condB) {
  //     X
  //   } else {
  //     Y
  //   }
  // }
  //
  // (Which is rendered as if/elseif/else)
  private static boolean ifElseChainDenesting(IfNode rtnode) {
    if (rtnode.innerType == EdgeType.DIRECT && rtnode.successorType != EdgeType.ELSE) {
      IfStatement outerIf = (IfStatement) rtnode.value;
      if (outerIf.getParent() instanceof SequenceStatement) {
        SequenceStatement parent = (SequenceStatement) outerIf.getParent();
        Statement nestedStat = rtnode.innerNode.value;

        // check that statements Y and Z (see above) jump to end
        boolean ifdirect = hasDirectEndEdge(nestedStat, parent);
        boolean elsedirect = hasDirectEndEdge(parent.getStats().getLast(), parent);
        if (ifdirect && elsedirect) {
          // check there is a nested if statement that doesn't have any exprents before it, and that statement X jumps to end
          IfStatement nestedIf = nestedStat instanceof IfStatement ? (IfStatement) nestedStat
            : nestedStat instanceof SequenceStatement && nestedStat.getFirst() instanceof IfStatement ? (IfStatement) nestedStat.getFirst() : null;
          if (nestedIf != null && nestedIf.getFirst().getExprents().isEmpty() && nestedIf.getIfstat() != null && hasDirectEndEdge(nestedIf.getIfstat(), parent)) {
            // check that statement Z is not an if statement (without exprents before it)
            List<StatEdge> successors = outerIf.getAllSuccessorEdges();
            Statement nextStat = !successors.isEmpty() && successors.get(0).getType() == StatEdge.TYPE_REGULAR ? successors.get(0).getDestination() : null;
            IfStatement nextIfStat = nextStat == null ? null : nextStat instanceof IfStatement ? (IfStatement) nextStat
              : nextStat instanceof SequenceStatement && nextStat.getFirst() instanceof IfStatement ? (IfStatement) nextStat.getFirst() : null;
            if (nextStat != null && (nextIfStat == null || !nextIfStat.getFirst().getExprents().isEmpty())) {
              // negate the condition and swap the branches
              IfExprent conditionExprent = outerIf.getHeadexprent();
              conditionExprent.setCondition(new FunctionExprent(FunctionType.BOOL_NOT, conditionExprent.getCondition(), null));
              swapBranches(outerIf, false, parent);

              // RTF: track that this transformation flipped the condition direction
              if (DecompilerContext.isRoundtripFidelity()) {
                outerIf.toggleRtfConditionFlipped();
              }

              return true;
            }
          }
        }
      }
    }

    return false;
  }

  // FIXME: rewrite the entire method!!! keep in mind finally exits!!
  private static boolean reorderIf(IfStatement ifstat) {
    if (ifstat.iftype == IfStatement.IFTYPE_IFELSE) {
      return false;
    }

    boolean ifdirect, elsedirect;
    boolean noifstat = false, noelsestat;
    boolean ifdirectpath = false, elsedirectpath = false;

    Statement parent = ifstat.getParent();
    Statement from = parent instanceof SequenceStatement ? parent : ifstat;

    Statement next = getNextStatement(from);

    if (ifstat.getIfstat() == null) {
      noifstat = true;

      ifdirect = ifstat.getIfEdge().getType() == StatEdge.TYPE_FINALLYEXIT ||
                 MergeHelper.isDirectPath(from, ifstat.getIfEdge().getDestination());
    } else {
      List<StatEdge> lstSuccs = ifstat.getIfstat().getAllSuccessorEdges();
      ifdirect = !lstSuccs.isEmpty() && lstSuccs.get(0).getType() == StatEdge.TYPE_FINALLYEXIT ||
                 hasDirectEndEdge(ifstat.getIfstat(), from);
    }

    Statement last = parent instanceof SequenceStatement ? parent.getStats().getLast() : ifstat;
    noelsestat = (last == ifstat);

    elsedirect = !last.getAllSuccessorEdges().isEmpty() && last.getAllSuccessorEdges().get(0).getType() == StatEdge.TYPE_FINALLYEXIT ||
                 hasDirectEndEdge(last, from);

    List<StatEdge> successors = ifstat.getAllSuccessorEdges();

    if (successors.isEmpty()) {
      // Can't have no successors- something went wrong horribly somewhere!
      throw new IllegalStateException("If statement " + ifstat + " has no successors!");
    }

    if (!noelsestat && existsPath(ifstat, successors.get(0).getDestination())) {
      return false;
    }

    if (!ifdirect && !noifstat) {
      ifdirectpath = existsPath(ifstat, next);
    }

    if (!elsedirect && !noelsestat) {
      SequenceStatement sequence = (SequenceStatement) parent;

      for (int i = sequence.getStats().size() - 1; i >= 0; i--) {
        Statement sttemp = sequence.getStats().get(i);
        if (sttemp == ifstat) {
          break;
        } else if (existsPath(sttemp, next)) {
          elsedirectpath = true;
          break;
        }
      }
    }

    if ((ifdirect || ifdirectpath) && (elsedirect || elsedirectpath) && !noifstat && !noelsestat) {  // if - then - else

      SequenceStatement sequence = (SequenceStatement) parent;

      // build and cut the new else statement
      List<Statement> lst = new ArrayList<>();
      for (int i = sequence.getStats().size() - 1; i >= 0; i--) {
        Statement sttemp = sequence.getStats().get(i);
        if (sttemp == ifstat) {
          break;
        } else {
          lst.add(0, sttemp);
        }
      }

      Statement stelse;
      if (lst.size() == 1) {
        stelse = lst.get(0);
      } else {
        stelse = new SequenceStatement(lst);
        stelse.setAllParent();
      }

      ifstat.removeSuccessor(ifstat.getFirstSuccessor());
      for (Statement st : lst) {
        sequence.getStats().removeWithKey(st.id);
      }

      StatEdge elseedge = new StatEdge(StatEdge.TYPE_REGULAR, ifstat.getFirst(), stelse);
      ifstat.getFirst().addSuccessor(elseedge);
      ifstat.setElsestat(stelse);
      ifstat.setElseEdge(elseedge);

      ifstat.getStats().addWithKey(stelse, stelse.id);
      stelse.setParent(ifstat);

      //			if(next.type != Statement.TYPE_DUMMYEXIT && (ifdirect || elsedirect)) {
      //	 			StatEdge breakedge = new StatEdge(StatEdge.TYPE_BREAK, ifstat, next);
      //				sequence.addLabeledEdge(breakedge);
      //				ifstat.addSuccessor(breakedge);
      //			}

      ifstat.iftype = IfStatement.IFTYPE_IFELSE;
    } else if (ifdirect && (!elsedirect || (noifstat && !noelsestat)) && !ifstat.getAllSuccessorEdges().isEmpty()) {  // if - then
      // RTF: preserve guard clauses - when the if-body terminates (return/throw) and
      // would be extracted from the if-statement, skip the reorder to keep the original
      // branch opcode. Only block the noelsestat=true path where the if-body extraction
      // is the sole structural change. The !noelsestat (swapBranches) path cannot be
      // safely blocked without causing type inference failures.
      if (noelsestat && !noifstat && isRtfGuardClause(ifstat)) {
        return false;
      }

      // RTF: block swapBranches when the if-body had a forward trailing goto.
      // Swapping eliminates the goto by reordering blocks (diff=-1).
      if (DecompilerContext.isRoundtripFidelity()) {
        Statement ifbody = ifstat.getIfstat();
        if (ifbody != null && rtfIfBodyHadTrailingGoto(ifbody)) {
          return false;
        }
      }

      // RTF: block inversion of merged loop guard clauses.
      // collapseIfIf merges separate if-conditions into a compound && with
      // a continue/break edge: if(a && b){continue;}. This is the correct form -
      // javac compiles it to separate branch instructions matching the original.
      // Inverting to if(a || b){body} changes the instruction count.
      // Only block when the head block had rtfFallthroughWasGoto, confirming the
      // original bytecode had separate if-statements with an explicit goto.
      if (DecompilerContext.isRoundtripFidelity() && noifstat) {
        StatEdge ifedge = ifstat.getIfEdge();
        if (ifedge != null && (ifedge.getType() == StatEdge.TYPE_CONTINUE
                            || ifedge.getType() == StatEdge.TYPE_BREAK)) {
          Statement head = ifstat.getFirst();
          if (head instanceof BasicBlockStatement
              && ((BasicBlockStatement) head).getBlock().rtfFallthroughWasGoto) {
            return false;
          }
        }
      }

      // negate the if condition
      IfExprent statexpr = ifstat.getHeadexprent();
      statexpr.setCondition(new FunctionExprent(FunctionType.BOOL_NOT, statexpr.getCondition(), null));

      // RTF: track that this transformation flipped the condition direction
      if (DecompilerContext.isRoundtripFidelity()) {
        ifstat.toggleRtfConditionFlipped();
      }

      if (noelsestat) {
        StatEdge ifedge = ifstat.getIfEdge();
        StatEdge elseedge = ifstat.getFirstSuccessor();

        if (noifstat) {
          ifstat.getFirst().removeSuccessor(ifedge);
          ifstat.removeSuccessor(elseedge);

          ifedge.setSource(ifstat);
          elseedge.setSource(ifstat.getFirst());

          ifstat.addSuccessor(ifedge);
          ifstat.getFirst().addSuccessor(elseedge);

          ifstat.setIfEdge(elseedge);
        } else {
          Statement ifbranch = ifstat.getIfstat();
          SequenceStatement newseq = new SequenceStatement(Arrays.asList(ifstat, ifbranch));

          ifstat.getFirst().removeSuccessor(ifedge);
          ifstat.getStats().removeWithKey(ifbranch.id);
          ifstat.setIfstat(null);

          ifstat.removeSuccessor(elseedge);
          elseedge.setSource(ifstat.getFirst());
          ifstat.getFirst().addSuccessor(elseedge);

          ifstat.setIfEdge(elseedge);

          ifstat.getParent().replaceStatement(ifstat, newseq);
          newseq.setAllParent();

          ifstat.addSuccessor(new StatEdge(StatEdge.TYPE_REGULAR, ifstat, ifbranch));
        }
      } else {
        swapBranches(ifstat, noifstat, (SequenceStatement) parent);
      }
    } else {
      return false;
    }

    return true;
  }

  private static void swapBranches(IfStatement ifstat, boolean noifstat, SequenceStatement parent) {
    ValidationHelper.validateTrue(ifstat.iftype == IfStatement.IFTYPE_IF, "This method is meant for swapping the branches of non if-else IfStatements");
    ifstat.toggleRtfIfBodyIsFallThrough(); // body semantics changed
    // build and cut the new else statement
    List<Statement> lst = new ArrayList<>();
    for (int i = parent.getStats().size() - 1; i >= 0; i--) {
      Statement sttemp = parent.getStats().get(i);
      if (sttemp == ifstat) {
        break;
      } else {
        lst.add(0, sttemp);
      }
    }

    Statement stelse;
    if (lst.size() == 1) {
      stelse = lst.get(0);
    } else {
      stelse = new SequenceStatement(lst);
      stelse.setAllParent();
    }

    ifstat.removeSuccessor(ifstat.getFirstSuccessor());
    for (Statement st : lst) {
      parent.getStats().removeWithKey(st.id);
    }

    if (noifstat) {
      StatEdge ifedge = ifstat.getIfEdge();

      ifstat.getFirst().removeSuccessor(ifedge);
      ifedge.setSource(ifstat);
      ifstat.addSuccessor(ifedge);
    } else {
      Statement ifbranch = ifstat.getIfstat();

      ifstat.getFirst().removeSuccessor(ifstat.getIfEdge());
      ifstat.getStats().removeWithKey(ifbranch.id);

      ifstat.addSuccessor(new StatEdge(StatEdge.TYPE_REGULAR, ifstat, ifbranch));

      parent.getStats().addWithKey(ifbranch, ifbranch.id);
      ifbranch.setParent(parent);
    }

    StatEdge newifedge = new StatEdge(StatEdge.TYPE_REGULAR, ifstat.getFirst(), stelse);
    ifstat.getFirst().addSuccessor(newifedge);
    ifstat.setIfstat(stelse);
    ifstat.setIfEdge(newifedge);

    ifstat.getStats().addWithKey(stelse, stelse.id);
    stelse.setParent(ifstat);
  }

  private static boolean hasDirectEndEdge(Statement stat, Statement from) {

    for (StatEdge edge : stat.getAllSuccessorEdges()) {
      if (MergeHelper.isDirectPath(from, edge.getDestination())) {
        return true;
      }
    }

    if (stat.getExprents() == null) {
      switch (stat.type) {
        case SEQUENCE:
          return hasDirectEndEdge(stat.getStats().getLast(), from);
        case CATCH_ALL:
        case TRY_CATCH:
          for (Statement st : stat.getStats()) {
            if (hasDirectEndEdge(st, from)) {
              return true;
            }
          }
          break;
        case IF:
          IfStatement ifstat = (IfStatement) stat;
          if (ifstat.iftype == IfStatement.IFTYPE_IFELSE) {
            return hasDirectEndEdge(ifstat.getIfstat(), from) ||
                   hasDirectEndEdge(ifstat.getElsestat(), from);
          }
          break;
        case SYNCHRONIZED:
          return hasDirectEndEdge(stat.getStats().get(1), from);
        case SWITCH:
          for (Statement st : stat.getStats()) {
            if (hasDirectEndEdge(st, from)) {
              return true;
            }
          }
      }
    }

    return false;
  }

  private static Statement getNextStatement(Statement stat) {
    Statement parent = stat.getParent();
    switch (parent.type) {
      case ROOT:
        return ((RootStatement) parent).getDummyExit();
      case DO:
        return parent;
      case SEQUENCE:
        SequenceStatement sequence = (SequenceStatement) parent;
        if (sequence.getStats().getLast() != stat) {
          for (int i = sequence.getStats().size() - 1; i >= 0; i--) {
            if (sequence.getStats().get(i) == stat) {
              return sequence.getStats().get(i + 1);
            }
          }
        }
    }

    return getNextStatement(parent);
  }

  private static boolean existsPath(Statement from, Statement to) {
    for (StatEdge edge : to.getAllPredecessorEdges()) {
      if (from.containsStatementStrict(edge.getSource())) {
        return true;
      }
    }

    return false;
  }
}