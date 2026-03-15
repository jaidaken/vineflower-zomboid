package org.jetbrains.java.decompiler.modules.decompiler;

import org.jetbrains.java.decompiler.modules.decompiler.exps.*;
import org.jetbrains.java.decompiler.modules.decompiler.stats.*;
import org.jetbrains.java.decompiler.struct.StructClass;

import java.util.ArrayList;
import java.util.List;

public class TryHelper {
  public static boolean enhanceTryStats(RootStatement root, StructClass cl) {
    boolean ret = makeTryWithResourceRec(cl, root);

    if (ret) {
      SequenceHelper.condenseSequences(root);

      if (!cl.getVersion().hasNewTryWithResources()) {
        if (collapseTryRec(root)) {
          SequenceHelper.condenseSequences(root);
        }
      }

      // NOTE: TWR temp return variable inlining is handled by inlineTwrReturnVars()
      // which is called from the main loop after StackVarsProcessor has simplified.
    }

    if (cl.getVersion().hasNewTryWithResources()) {
      if (mergeTrys(root)) {
        SequenceHelper.condenseSequences(root);

        ret = true;
      }
    }

    return ret;
  }

  private static boolean makeTryWithResourceRec(StructClass cl, Statement stat) {
    if (cl.getVersion().hasNewTryWithResources()) {
      boolean ret = false;
      if (stat instanceof CatchStatement) {
        if (TryWithResourcesProcessor.makeTryWithResourceJ11((CatchStatement) stat)) {
          ret = true;
        }
      }

      for (Statement st : new ArrayList<>(stat.getStats())) {
        if (makeTryWithResourceRec(cl, st)) {
          ret = true;
        }
      }

      return ret;
    } else {
      if (stat instanceof CatchAllStatement && ((CatchAllStatement) stat).isFinally()) {
        if (TryWithResourcesProcessor.makeTryWithResource((CatchAllStatement) stat)) {
          return true;
        }
      }

      for (Statement st : new ArrayList<>(stat.getStats())) {
        if (makeTryWithResourceRec(cl, st)) {
          return true;
        }
      }

      return false;
    }
  }

  // J11+
  // Merge all try statements recursively
  private static boolean mergeTrys(Statement root) {
    boolean ret = false;

    if (root instanceof CatchStatement) {
      if (mergeTry((CatchStatement) root)) {
        ret = true;
      }
    }

    for (Statement stat : new ArrayList<>(root.getStats())) {
      ret |= mergeTrys(stat);
    }

    return ret;
  }

  // J11+
  // Merges try with resource statements that are nested within each other, as well as try with resources statements nested in a normal try.
  private static boolean mergeTry(CatchStatement stat) {
    if (stat.getStats().isEmpty()) {
      return false;
    }

    // Get the statement inside of the current try
    Statement inner = stat.getStats().get(0);

    // Check if the inner statement is a try statement
    if (inner instanceof CatchStatement) {
      // Filter on try with resources statements
      List<Exprent> resources = ((CatchStatement) inner).getResources();
      if (!resources.isEmpty()) {
        // One try inside of the catch

        // Only merge trys that have an inner statement size of 1, a single block
        // TODO: how does this handle nested nullable try stats?
        if (inner.getStats().size() == 1) {
          // Set the outer try to be resources, and initialize
          stat.getResources().addAll(resources);
          stat.getVarDefinitions().addAll(inner.getVarDefinitions());

          // Get inner block of inner try stat
          Statement innerBlock = inner.getStats().get(0);

          // Remove successors as the replaceStatement call will add the appropriate successor
          List<StatEdge> innerEdges = inner.getAllSuccessorEdges();
          for (StatEdge succ : innerBlock.getAllSuccessorEdges()) {
            boolean found = false;
            for (StatEdge innerEdge : innerEdges) {
              if (succ.getDestination() == innerEdge.getDestination() && succ.getType() == innerEdge.getType()) {
                found = true;
                break;
              }
            }

            if (found) {
              innerBlock.removeSuccessor(succ);
            }
          }

          // Replace the inner try statement with the block inside
          stat.replaceStatement(inner, innerBlock);

          return true;
        }
      }
    }

    return false;
  }

  // Inline temp return variables left over from try-with-resources desugaring.
  //
  // After JDK 9+ try-with-resources reconstruction, we may have:
  //   try (...) { ...; var = value; }
  //   return var;
  // This inlines it to:
  //   try (...) { ...; return value; }
  //
  public static boolean inlineTwrReturnVars(Statement stat) {
    boolean changed = false;

    for (Statement st : new ArrayList<>(stat.getStats())) {
      if (inlineTwrReturnVars(st)) {
        changed = true;
      }
    }

    if (stat instanceof SequenceStatement) {
      for (int i = 0; i < stat.getStats().size() - 1; i++) {
        Statement curr = stat.getStats().get(i);
        Statement next = stat.getStats().get(i + 1);

        // Check: curr is a try-with-resources (CatchStatement with resources)
        // and next is a basic block with a single return expression
        if (curr instanceof CatchStatement catchStat
            && !catchStat.getResources().isEmpty()
            && next instanceof BasicBlockStatement
            && next.getExprents() != null
            && next.getExprents().size() == 1
            && next.getExprents().get(0) instanceof ExitExprent exitExpr
            && exitExpr.getExitType() == ExitExprent.Type.RETURN
            && exitExpr.getValue() instanceof VarExprent returnVar) {

          // Find the last basic block in the try body that ends with an
          // assignment to the same variable
          Statement tryBody = catchStat.getFirst();
          Statement lastInBody = findLastStatement(tryBody);

          if (lastInBody != null
              && lastInBody.getExprents() != null
              && !lastInBody.getExprents().isEmpty()) {
            List<Exprent> bodyExprents = lastInBody.getExprents();
            Exprent lastExpr = bodyExprents.get(bodyExprents.size() - 1);

            if (lastExpr instanceof AssignmentExprent assignment
                && assignment.getCondType() == null
                && assignment.getLeft() instanceof VarExprent assignVar
                && assignVar.equals(returnVar)) {

              // Replace the assignment with a return of the assigned value
              ExitExprent newReturn = (ExitExprent) exitExpr.copy();
              newReturn.replaceExprent(newReturn.getValue(), assignment.getRight().copy());
              bodyExprents.set(bodyExprents.size() - 1, newReturn);

              // Remove the return statement after the try
              next.getExprents().clear();
              changed = true;
            }
          }
        }
      }
    }

    return changed;
  }

  // Walk the statement tree to find the last statement in the normal
  // execution path (the deepest "last" statement in a chain of sequences).
  private static Statement findLastStatement(Statement stat) {
    if (stat instanceof SequenceStatement) {
      Statement last = stat.getStats().get(stat.getStats().size() - 1);
      return findLastStatement(last);
    }

    // For try/try-with-resources, the last statement in the try body
    // is the last in the normal execution path.
    if (stat instanceof CatchStatement) {
      return findLastStatement(((CatchStatement) stat).getFirst());
    }

    // For if statements where the if-body returns and the fall-through
    // continues, the last statement is the statement itself (which may
    // have exprents after the if).
    if (stat.getExprents() != null) {
      return stat;
    }

    // For compound statements without exprents (like an if-then without
    // else), return null - we can't safely determine the last expression.
    return null;
  }

  private static boolean collapseTryRec(Statement stat) {
    if (stat instanceof CatchStatement && collapseTry((CatchStatement)stat)) {
      return true;
    }

    for (Statement st : stat.getStats()) {
      if (collapseTryRec(st)) {
        return true;
      }
    }

    return false;
  }

  private static boolean collapseTry(CatchStatement catchStat) {
    Statement parent = catchStat;
    if (parent.getFirst() != null && parent.getFirst() instanceof SequenceStatement) {
      parent = parent.getFirst();
    }
    if (parent != null && parent.getFirst() != null && parent.getFirst() instanceof CatchStatement) {
      CatchStatement toRemove = (CatchStatement)parent.getFirst();

      List<Exprent> resources = toRemove.getResources();
      if (!resources.isEmpty()) {
        catchStat.getResources().addAll(resources);

        catchStat.getVarDefinitions().addAll(toRemove.getVarDefinitions());
        parent.replaceStatement(toRemove, toRemove.getFirst());

        if (!toRemove.getVars().isEmpty()) {
          for (int i = 0; i < toRemove.getVars().size(); ++i) {
            catchStat.getVars().add(i, toRemove.getVars().get(i));
            catchStat.getExctStrings().add(i, toRemove.getExctStrings().get(i));

            catchStat.getStats().add(i + 1, catchStat.getStats().get(i + 1));
          }
        }
        return true;
      }
    }
    return false;
  }
}
