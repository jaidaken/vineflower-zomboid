// Copyright 2000-2024 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.modules.decompiler;

import org.jetbrains.java.decompiler.modules.decompiler.exps.*;
import org.jetbrains.java.decompiler.modules.decompiler.stats.*;

import java.util.ArrayList;
import java.util.List;

/**
 * Eliminates dead variable stores in RTF mode.
 * <p>
 * A dead store is an assignment where:
 * 1. The left side is a VarExprent
 * 2. The right side is a pure expression (VarExprent or ConstExprent) with no side effects
 * 3. The left-side variable is never referenced (read or written) anywhere else in the method
 * <p>
 * These dead stores originate from bytecode patterns like {@code aload X; astore Y} where
 * the compiler copied a value to a local slot that was never subsequently read. javac
 * eliminates these on recompilation, producing fewer instructions.
 */
public final class DeadStoreEliminator {

  private DeadStoreEliminator() {
  }

  /**
   * Remove dead stores from the statement tree.
   *
   * @param root the root statement of the method
   * @return true if any dead stores were removed
   */
  public static boolean eliminateDeadStores(Statement root) {
    boolean changed = false;

    // Collect all dead store assignments first, then remove them.
    // This avoids concurrent modification while iterating.
    List<DeadStore> deadStores = new ArrayList<>();
    collectDeadStores(root, root, deadStores);

    for (DeadStore ds : deadStores) {
      List<Exprent> exprents = ds.container.getExprents();
      if (exprents != null && exprents.remove(ds.assignment)) {
        changed = true;
      }
      // Also check varDefinitions
      List<Exprent> varDefs = ds.container.getVarDefinitions();
      if (varDefs != null && varDefs.remove(ds.assignment)) {
        changed = true;
      }
    }

    return changed;
  }

  /**
   * Recursively collect dead store assignments.
   */
  private static void collectDeadStores(Statement stat, Statement root, List<DeadStore> result) {
    // Check exprents in this statement
    if (stat.getExprents() != null) {
      for (Exprent expr : stat.getExprents()) {
        if (isDeadStore(expr, root)) {
          result.add(new DeadStore(stat, expr));
        }
      }
    }

    // Check varDefinitions
    for (Exprent expr : stat.getVarDefinitions()) {
      if (isDeadStore(expr, root)) {
        result.add(new DeadStore(stat, expr));
      }
    }

    // Recurse into children
    for (Statement child : stat.getStats()) {
      collectDeadStores(child, root, result);
    }
  }

  /**
   * Check if an expression is a dead store: an assignment to a variable
   * from a pure expression, where the assigned variable is never referenced
   * elsewhere in the method.
   */
  private static boolean isDeadStore(Exprent expr, Statement root) {
    if (!(expr instanceof AssignmentExprent)) {
      return false;
    }

    AssignmentExprent assign = (AssignmentExprent) expr;

    // Left side must be a variable
    if (!(assign.getLeft() instanceof VarExprent)) {
      return false;
    }

    // Right side must be a pure expression (no side effects)
    if (!isPureExpression(assign.getRight())) {
      return false;
    }

    VarExprent leftVar = (VarExprent) assign.getLeft();
    int varIndex = leftVar.getIndex();

    // The variable must not be referenced anywhere else in the method
    return !isVariableReferencedElsewhere(root, varIndex, expr);
  }

  /**
   * Check if an expression is pure (no side effects).
   * Only variable loads and constants are considered pure.
   */
  private static boolean isPureExpression(Exprent expr) {
    return expr instanceof VarExprent || expr instanceof ConstExprent;
  }

  /**
   * Check if a variable is referenced (read or assigned) anywhere in the
   * statement tree, excluding the given expression.
   */
  private static boolean isVariableReferencedElsewhere(Statement stat, int varIndex, Exprent excludeExpr) {
    // Check exprents
    if (stat.getExprents() != null) {
      for (Exprent expr : stat.getExprents()) {
        if (expr == excludeExpr) continue;
        if (exprReferencesVar(expr, varIndex)) return true;
      }
    }

    // Check var definitions
    for (Exprent expr : stat.getVarDefinitions()) {
      if (expr == excludeExpr) continue;
      if (exprReferencesVar(expr, varIndex)) return true;
    }

    // Check DoStatement special exprents (init, condition, increment)
    if (stat instanceof DoStatement) {
      DoStatement doStat = (DoStatement) stat;
      Exprent init = doStat.getInitExprent();
      if (init != null && init != excludeExpr && exprReferencesVar(init, varIndex)) return true;
      Exprent cond = doStat.getConditionExprent();
      if (cond != null && cond != excludeExpr && exprReferencesVar(cond, varIndex)) return true;
      Exprent inc = doStat.getIncExprent();
      if (inc != null && inc != excludeExpr && exprReferencesVar(inc, varIndex)) return true;
    }

    // Check IfStatement head exprent (condition)
    if (stat instanceof IfStatement) {
      IfExprent headExpr = ((IfStatement) stat).getHeadexprent();
      if (headExpr != null && headExpr != excludeExpr && exprReferencesVar(headExpr, varIndex)) return true;
    }

    // Check SwitchStatement head exprent
    if (stat instanceof SwitchStatement) {
      Exprent headExpr = ((SwitchStatement) stat).getHeadexprent();
      if (headExpr != null && headExpr != excludeExpr && exprReferencesVar(headExpr, varIndex)) return true;
    }

    // Check SynchronizedStatement head exprent
    if (stat instanceof SynchronizedStatement) {
      Exprent headExpr = ((SynchronizedStatement) stat).getHeadexprent();
      if (headExpr != null && headExpr != excludeExpr && exprReferencesVar(headExpr, varIndex)) return true;
    }

    // Recurse into children
    for (Statement child : stat.getStats()) {
      if (isVariableReferencedElsewhere(child, varIndex, excludeExpr)) return true;
    }

    return false;
  }

  /**
   * Check if any VarExprent in the expression tree references the given variable index.
   */
  private static boolean exprReferencesVar(Exprent expr, int varIndex) {
    if (expr instanceof VarExprent && ((VarExprent) expr).getIndex() == varIndex) return true;
    for (Exprent sub : expr.getAllExprents(true)) {
      if (sub instanceof VarExprent && ((VarExprent) sub).getIndex() == varIndex) return true;
    }
    return false;
  }

  /**
   * Holds a reference to a dead store assignment and its containing statement.
   */
  private static final class DeadStore {
    final Statement container;
    final Exprent assignment;

    DeadStore(Statement container, Exprent assignment) {
      this.container = container;
      this.assignment = assignment;
    }
  }
}
