// Copyright 2000-2024 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.modules.decompiler;

import org.jetbrains.java.decompiler.main.DecompilerContext;
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

  public static boolean eliminateDeadCode(Statement root) {
    boolean changed = false;

    List<Statement> children = new ArrayList<>(root.getStats());
    for (Statement child : children) {
      if (eliminateDeadCode(child)) {
        changed = true;
      }
    }

    if (root instanceof SequenceStatement) {
      if (root.getParent() instanceof SwitchStatement) {
        return changed;
      }
      if (removeDeadTail(root)) {
        changed = true;
      }
    }

    return changed;
  }

  private static boolean removeDeadTail(Statement seq) {
    VBStyleCollection<Statement, Integer> stats = seq.getStats();

    if (stats.size() < 2) {
      return false;
    }

    boolean changed = false;

    for (int i = 0; i < stats.size() - 1; i++) {
      Statement stat = stats.get(i);

      if (!isUnconditionalExit(stat)) {
        continue;
      }

      // stat unconditionally exits; check subsequent statements for removal.
      // Work backwards from the end to avoid index shifting issues.
      for (int j = stats.size() - 1; j > i; j--) {
        Statement dead = stats.get(j);

        if (hasIncomingEdgesFromLiveCode(dead, seq, i)) {
          // This statement is a jump target from live code; stop removing
          break;
        }

        for (StatEdge edge : new ArrayList<>(dead.getAllSuccessorEdges())) {
          dead.removeSuccessor(edge);
        }
        for (StatEdge edge : new ArrayList<>(dead.getAllPredecessorEdges())) {
          edge.getSource().removeSuccessor(edge);
        }
        for (StatEdge edge : new ArrayList<>(dead.getLabelEdges())) {
          edge.closure = null;
        }
        dead.getLabelEdges().clear();

        stats.removeWithKey(dead.id);
        changed = true;
      }

      if (changed) {
        break;
      }
    }

    return changed;
  }

  private static boolean isUnconditionalExit(Statement stat) {
    if (stat.hasBasicSuccEdge()) {
      List<StatEdge> regularSuccs = stat.getSuccessorEdges(StatEdge.TYPE_REGULAR);
      if (!regularSuccs.isEmpty()) {
        // In RTF mode, check if the statement also has break/continue edges
        // or if its exprents contain a return/throw (exprent-level control transfer
        // that the statement edge graph doesn't reflect).
        if (DecompilerContext.isRoundtripFidelity()) {
          List<StatEdge> breakSuccs = stat.getSuccessorEdges(StatEdge.TYPE_BREAK);
          List<StatEdge> contSuccs = stat.getSuccessorEdges(StatEdge.TYPE_CONTINUE);
          if (!breakSuccs.isEmpty() || !contSuccs.isEmpty()) {
            return true;
          }
          for (StatEdge edge : stat.getAllDirectSuccessorEdges()) {
            if (edge.getType() != StatEdge.TYPE_REGULAR) {
              return true;
            }
          }
          // Check if the PARENT sequence or loop has a continue/break edge
          // that makes this the effective last statement
          Statement parent = stat.getParent();
          if (parent != null) {
            for (StatEdge pedge : parent.getAllDirectSuccessorEdges()) {
              if (pedge.getType() != StatEdge.TYPE_REGULAR) {
                // Parent has a non-regular edge (continue/break)
                // If this statement is the last in the parent's stats,
                // everything after it in the outer sequence is unreachable
                if (parent.getStats().getLast() == stat) {
                  return true;
                }
              }
            }
          }
        }
        return false;
      }

      List<StatEdge> directSuccs = stat.getAllDirectSuccessorEdges();
      if (directSuccs.isEmpty()) {
        return false;
      }

      return true;
    }

    return true;
  }

  /**
   * Check whether a statement has incoming edges from live code, meaning it
   * cannot be safely removed. "Live code" means either:
   * (a) code outside the sequence entirely, or
   * (b) code in the sequence at or before the unconditional exit (index <= cutIndex)
   *
   * Edges from other dead code (after the cut index) do not block removal.
   */
  private static boolean hasIncomingEdgesFromLiveCode(Statement stat, Statement seq, int cutIndex) {
    // Check predecessor edges.
    Set<Statement> preds = stat.getNeighboursSet(Statement.STATEDGE_DIRECT_ALL, EdgeDirection.BACKWARD);
    for (Statement pred : preds) {
      if (!seq.containsStatementStrict(pred)) {
        return true; // from outside the sequence
      }
      if (isInLivePart(pred, seq, cutIndex)) {
        return true; // from live code
      }
    }

    // Check label edges (this statement is the closure/target).
    // These represent genuine closure relationships — removing the target
    // would invalidate the break/continue label reference.
    for (StatEdge labelEdge : stat.getLabelEdges()) {
      Statement source = labelEdge.getSource();
      if (!seq.containsStatementStrict(source)) {
        return true; // source from outside
      }
      if (isInLivePart(source, seq, cutIndex)) {
        return true; // source from live code
      }
    }

    return false;
  }

  /**
   * Check if a statement is contained within the live part of a sequence,
   * meaning it is nested inside a child at index <= cutIndex.
   */
  private static boolean isInLivePart(Statement source, Statement seq, int cutIndex) {
    VBStyleCollection<Statement, Integer> stats = seq.getStats();
    for (int k = 0; k <= cutIndex && k < stats.size(); k++) {
      if (stats.get(k).containsStatement(source)) {
        return true;
      }
    }
    return false;
  }
}
