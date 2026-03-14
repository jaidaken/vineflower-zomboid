// Copyright 2000-2024 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.modules.decompiler;

import org.jetbrains.java.decompiler.modules.decompiler.stats.SequenceStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.Statement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.Statement.EdgeDirection;
import org.jetbrains.java.decompiler.modules.decompiler.stats.SwitchStatement;
import org.jetbrains.java.decompiler.util.collections.VBStyleCollection;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

/**
 * Eliminates dead (unreachable) code in sequence statements.
 * <p>
 * In roundtrip fidelity (RTF) mode, condition negation is blocked in IfHelper
 * to preserve original bytecode branch direction. This can leave unreachable
 * statements after unconditional control flow transfers (return, break,
 * continue, throw), which javac rejects as "unreachable statement".
 * <p>
 * This pass walks each SequenceStatement bottom-up and removes trailing
 * unreachable statements that follow an unconditional exit point.
 */
public final class DeadCodeEliminator {

  private DeadCodeEliminator() {
  }

  /**
   * Recursively eliminate dead code from the statement tree.
   *
   * @param root the root of the statement tree to process
   * @return true if any dead code was removed
   */
  public static boolean eliminateDeadCode(Statement root) {
    boolean changed = false;

    // Process children first (bottom-up) so inner sequences are cleaned
    // before outer ones. Use a snapshot to avoid concurrent modification.
    List<Statement> children = new ArrayList<>(root.getStats());
    for (Statement child : children) {
      if (eliminateDeadCode(child)) {
        changed = true;
      }
    }

    if (root instanceof SequenceStatement) {
      // Do not eliminate dead code inside switch case sequences — break
      // statements in switch cases are NOT unconditional exits for siblings
      if (root.getParent() instanceof SwitchStatement) {
        return changed;
      }
      if (removeDeadTail(root)) {
        changed = true;
      }
    }

    return changed;
  }

  /**
   * For a SequenceStatement, find the first statement that unconditionally
   * exits (does not fall through to the next statement), then remove all
   * subsequent statements that are not reachable from elsewhere.
   *
   * @param seq the sequence statement to process
   * @return true if any statements were removed
   */
  private static boolean removeDeadTail(Statement seq) {
    VBStyleCollection<Statement, Integer> stats = seq.getStats();

    if (stats.size() < 2) {
      return false;
    }

    boolean changed = false;

    // Scan forward through the sequence looking for an unconditional exit
    for (int i = 0; i < stats.size() - 1; i++) {
      Statement stat = stats.get(i);

      if (!isUnconditionalExit(stat)) {
        continue;
      }

      // stat unconditionally exits; check subsequent statements for removal
      // Work backwards from the end to avoid index shifting issues
      for (int j = stats.size() - 1; j > i; j--) {
        Statement dead = stats.get(j);

        if (hasIncomingEdgesFromOutside(dead, seq)) {
          // This statement is a jump target from elsewhere; stop removing
          break;
        }

        // Remove all edges from/to this dead statement
        for (StatEdge edge : new ArrayList<>(dead.getAllSuccessorEdges())) {
          dead.removeSuccessor(edge);
        }
        for (StatEdge edge : new ArrayList<>(dead.getAllPredecessorEdges())) {
          edge.getSource().removeSuccessor(edge);
        }
        // Remove label edges that reference this dead statement
        for (StatEdge edge : new ArrayList<>(dead.getLabelEdges())) {
          edge.closure = null;
        }
        dead.getLabelEdges().clear();

        stats.removeWithKey(dead.id);
        changed = true;
      }

      if (changed) {
        // Update the sequence's lastBasicType based on the new last element
        break;
      }
    }

    return changed;
  }

  /**
   * Determine whether a statement is an unconditional control flow transfer,
   * meaning execution can never fall through to the next statement in the
   * sequence.
   * <p>
   * This returns true when the statement:
   * <ul>
   *   <li>Does not have a basic successor edge (e.g., infinite loop, if-else
   *       where both branches exit)</li>
   *   <li>Has no regular-type successor edges (only break/continue/exception
   *       edges that jump elsewhere)</li>
   * </ul>
   */
  private static boolean isUnconditionalExit(Statement stat) {
    // hasBasicSuccEdge() returns false for statements that never fall through:
    //   - Infinite loops (DoStatement with INFINITE type)
    //   - If-else statements (both branches covered)
    //   - Most compound statements by default
    // But BasicBlockStatement always returns true, even when it ends with
    // return/throw, because it always has a successor edge (break to dummy exit).
    //
    // So we also need to check that there are no regular successor edges,
    // which would indicate normal fall-through control flow.
    if (stat.hasBasicSuccEdge()) {
      // The statement type says it can fall through. Check if it actually
      // has regular edges (indicating fall-through) vs only break/continue.
      List<StatEdge> regularSuccs = stat.getSuccessorEdges(StatEdge.TYPE_REGULAR);
      if (!regularSuccs.isEmpty()) {
        return false;
      }

      // No regular successors. Check for explicit break/continue edges
      // which indicate control transfer (return, break, continue, throw).
      List<StatEdge> directSuccs = stat.getAllDirectSuccessorEdges();
      if (directSuccs.isEmpty()) {
        // No successors at all means it doesn't exit (shouldn't normally happen)
        return false;
      }

      // All direct successors are break/continue/finallyexit edges,
      // so this statement unconditionally transfers control elsewhere.
      return true;
    }

    // Statement type itself says no fall-through (e.g., infinite loop, if-else)
    return true;
  }

  /**
   * Check whether a statement has incoming edges from statements that are
   * NOT its predecessor in the same sequence. Such edges indicate the
   * statement is a label/jump target and should not be removed.
   *
   * @param stat the statement to check
   * @param seq  the parent sequence statement
   * @return true if the statement has incoming edges from outside the
   *         normal sequence flow
   */
  private static boolean hasIncomingEdgesFromOutside(Statement stat, Statement seq) {
    // Check all predecessor edges (all types including break, continue, etc.)
    Set<Statement> preds = stat.getNeighboursSet(Statement.STATEDGE_DIRECT_ALL, EdgeDirection.BACKWARD);

    for (Statement pred : preds) {
      // If the predecessor is not in the same sequence, this statement is
      // a jump target from outside
      if (!seq.containsStatementStrict(pred)) {
        return true;
      }
    }

    // Also check if this statement is a label edge target (closure target)
    // Label edges on this statement mean something jumps to/through it
    if (!stat.getLabelEdges().isEmpty()) {
      for (StatEdge labelEdge : stat.getLabelEdges()) {
        // If the label edge source is outside the sequence, it's reachable
        if (!seq.containsStatementStrict(labelEdge.getSource())) {
          return true;
        }
      }
    }

    return false;
  }
}
