// Copyright 2000-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.modules.decompiler.stats;

import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.modules.decompiler.DecHelper;
import org.jetbrains.java.decompiler.modules.decompiler.ExprProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.StatEdge;
import org.jetbrains.java.decompiler.util.TextBuffer;
import org.jetbrains.java.decompiler.util.collections.VBStyleCollection;

import java.util.Arrays;
import java.util.List;


public class SequenceStatement extends Statement {


  // *****************************************************************************
  // constructors
  // *****************************************************************************

  protected SequenceStatement() {
    super(StatementType.SEQUENCE);
  }

  public SequenceStatement(Statement... stats) {
    this(Arrays.asList(stats));
  }

  public SequenceStatement(List<? extends Statement> lst) {

    this();

    lastBasicType = lst.get(lst.size() - 1).getLastBasicType();

    for (Statement st : lst) {
      stats.addWithKey(st, st.id);
    }

    first = stats.get(0);
  }

  protected SequenceStatement(Statement head, Statement tail) {

    this(Arrays.asList(head, tail));

    List<StatEdge> lstSuccs = tail.getSuccessorEdges(STATEDGE_DIRECT_ALL);
    if (!lstSuccs.isEmpty()) {
      StatEdge edge = lstSuccs.get(0);

      if (edge.getType() == StatEdge.TYPE_REGULAR && edge.getDestination() != head) {
        post = edge.getDestination();
      }
    }
  }


  // *****************************************************************************
  // public methods
  // *****************************************************************************

  public static Statement isHead2Block(Statement head) {

    if (head.getLastBasicType() != LastBasicType.GENERAL) {
      return null;
    }

    // at most one outgoing edge
    StatEdge edge = null;
    List<StatEdge> lstSuccs = head.getSuccessorEdges(STATEDGE_DIRECT_ALL);
    if (!lstSuccs.isEmpty()) {
      edge = lstSuccs.get(0);
    }

    if (edge != null && edge.getType() == StatEdge.TYPE_REGULAR) {
      Statement stat = edge.getDestination();

      if (stat != head && stat.getPredecessorEdges(StatEdge.TYPE_REGULAR).size() == 1
          && !stat.isMonitorEnter()) {

        if (stat.getLastBasicType() == LastBasicType.GENERAL) {
          if (DecHelper.checkStatementExceptions(Arrays.asList(head, stat))) {
            return new SequenceStatement(head, stat);
          }
        }
      }
    }

    return null;
  }

  @Override
  public TextBuffer toJava(int indent) {
    TextBuffer buf = new TextBuffer();
    boolean islabeled = isLabeled();

    buf.append(ExprProcessor.listToJava(varDefinitions, indent));

    if (islabeled) {
      buf.appendIndent(indent++).append("label").append(this.id).append(": {").appendLineSeparator();
    }

    boolean notempty = false;

    for (int i = 0; i < stats.size(); i++) {

      Statement st = stats.get(i);

      TextBuffer str = ExprProcessor.jmpWrapper(st, indent, false);

      if (i > 0 && !str.containsOnlyWhitespaces() && notempty) {
        buf.appendLineSeparator();
      }

      buf.append(str);

      notempty = !str.containsOnlyWhitespaces();

      // RTF: if this child always exits via a non-regular path (continue/break/
      // return/throw), subsequent children are bytecode-level dead code that
      // javac would reject as "unreachable statement". Stop rendering.
      if (DecompilerContext.isRoundtripFidelity() && i < stats.size() - 1
          && endsWithNonRegularExit(st)) {
        // Safety check: if the next child is the destination of a break edge
        // from within the current child, a control-flow path reaches it and
        // it must not be suppressed. This happens when an IfStatement (or
        // other branching statement) has one branch that exits and another
        // that falls through - the fall-through becomes a TYPE_BREAK edge
        // during collapseNodesToStatement, making the next sibling reachable.
        Statement nextChild = stats.get(i + 1);
        if (!hasBreakEdgeFromWithin(st, nextChild)) {
          break;
        }
      }

      // RTF: a try-finally can make subsequent siblings unreachable in two ways:
      // 1. The finally handler itself returns, overriding any try-body completion.
      // 2. All paths in the try body return/throw, so the finally just cleans up
      //    and the method exits from within the try-finally.
      // For case 1, check if the handler ends with a return (not throw — throw
      // is normal re-throw behavior for finally handlers).
      // For case 2, check if the CatchAllStatement has no successor edges AND
      // all paths in the try body actually exit. Just checking for empty successor
      // edges is insufficient — a try-catch-finally where the catch branch doesn't
      // return will have no successor edges but still needs a trailing return.
      if (DecompilerContext.isRoundtripFidelity() && i < stats.size() - 1
          && st instanceof CatchAllStatement && ((CatchAllStatement) st).isFinally()) {
        CatchAllStatement cas = (CatchAllStatement) st;
        if (handlerEndsWithReturn(cas.getHandler())
            || (cas.getSuccessorEdges(STATEDGE_DIRECT_ALL).isEmpty()
                && allPathsExit(cas.getFirst()))) {
          break;
        }
      }
    }

    if (islabeled) {
      buf.appendIndent(indent-1).append("}").appendLineSeparator();
    }

    return buf;
  }

  /**
   * Check if a statement's execution always ends with a non-regular exit
   * (continue/break/return/throw). This is determined by checking the
   * statement's jmpWrapper condition: exactly 1 direct successor edge that
   * is not TYPE_REGULAR and is explicit.
   *
   * For SequenceStatements, this recursively checks the last child, since
   * the sequence's execution ends with its last child's exit.
   *
   * For IfStatements, both branches must end with non-regular exits for the
   * code after the if to be unreachable. A single exiting branch does not
   * make subsequent code unreachable — the other branch falls through.
   */
  private static boolean endsWithNonRegularExit(Statement stat) {
    // For IfStatements: analyze branch structure instead of relying on
    // the edge check alone. An if-else only makes subsequent code unreachable
    // if BOTH branches exit. An if-without-else always has a fall-through
    // path (when the condition is false).
    if (stat instanceof IfStatement) {
      IfStatement ifStat = (IfStatement) stat;
      if (ifStat.iftype == IfStatement.IFTYPE_IFELSE) {
        // Both branches must end with non-regular exits
        Statement ifBody = ifStat.getIfstat();
        Statement elseBody = ifStat.getElsestat();
        return ifBody != null && elseBody != null
            && endsWithNonRegularExit(ifBody)
            && endsWithNonRegularExit(elseBody);
      }
      // IFTYPE_IF: the false-path is the IfStatement's own successor edge.
      // Both the if-body AND the false-path must exit for subsequent code
      // to be unreachable.
      List<StatEdge> ifSuccs = stat.getSuccessorEdges(STATEDGE_DIRECT_ALL);
      if (ifSuccs.size() == 1) {
        StatEdge edge = ifSuccs.get(0);
        if (edge.getType() != StatEdge.TYPE_REGULAR && edge.explicit) {
          // False-path exits via break/continue. Also require if-body to exit.
          Statement ifBody = ifStat.getIfstat();
          return ifBody != null && endsWithNonRegularExit(ifBody);
        }
      }
      return false;
    }

    // Check the statement's own direct successor edges (same condition as jmpWrapper)
    List<StatEdge> succs = stat.getSuccessorEdges(STATEDGE_DIRECT_ALL);
    if (succs.size() == 1) {
      StatEdge edge = succs.get(0);
      if (edge.getType() != StatEdge.TYPE_REGULAR && edge.explicit) {
        return true;
      }
    }

    // A SwitchStatement with an explicit default case and no outgoing successor
    // edges where ALL case bodies end with a non-regular exit: all execution
    // paths exit via throw/return, so subsequent siblings are unreachable.
    // We must verify every case body actually exits — a case containing a nested
    // switch with fall-through paths (e.g., unsimplified string-switch hashCode
    // patterns) may not exit on all paths even though the switch has no successor
    // edges in the edge graph.
    if (succs.isEmpty() && stat instanceof SwitchStatement) {
      SwitchStatement sw = (SwitchStatement) stat;
      boolean hasExplicitDefault = false;
      for (List<StatEdge> edges : sw.getCaseEdges()) {
        for (StatEdge edge : edges) {
          if (edge == sw.getDefaultEdge()) {
            hasExplicitDefault = true;
            break;
          }
        }
        if (hasExplicitDefault) break;
      }
      if (hasExplicitDefault) {
        // Verify the last case body ends with a non-regular exit.
        // Cases that don't exit on their own fall through to subsequent cases.
        // If the last case exits, all fall-through chains eventually reach an exit.
        // If the last case doesn't exit, some paths fall off the switch.
        List<Statement> caseStats = sw.getCaseStatements();
        if (!caseStats.isEmpty()
            && endsWithNonRegularExit(caseStats.get(caseStats.size() - 1))) {
          return true;
        }
      }
    }

    // For sequence statements, check the last child recursively
    if (stat instanceof SequenceStatement) {
      VBStyleCollection<Statement, Integer> children = stat.getStats();
      if (!children.isEmpty()) {
        return endsWithNonRegularExit(children.getLast());
      }
    }

    // Check if the statement has exprents ending with a return/throw
    // (ExitExprent with EXIT_RETURN or EXIT_THROW)
    if (stat.getExprents() != null && !stat.getExprents().isEmpty()) {
      Object lastExpr = stat.getExprents().get(stat.getExprents().size() - 1);
      if (lastExpr instanceof org.jetbrains.java.decompiler.modules.decompiler.exps.ExitExprent) {
        return true;
      }
    }

    // RTF: while(true) with try-finally in the body is an unconditional exit.
    // The finally handler's rethrow path creates a spurious successor edge out of
    // the loop, but Java semantics say code after while(true) is unreachable.
    // Only trigger when the loop body contains a try-finally to avoid broad regressions.
    if (stat instanceof DoStatement
        && ((DoStatement) stat).getLooptype() == DoStatement.Type.INFINITE
        && bodyContainsTryFinally(stat)) {
      return true;
    }

    return false;
  }

  private static boolean bodyContainsTryFinally(Statement stat) {
    if (stat instanceof CatchAllStatement && ((CatchAllStatement) stat).isFinally()) {
      return true;
    }
    for (Statement child : stat.getStats()) {
      if (child instanceof CatchAllStatement && ((CatchAllStatement) child).isFinally()) {
        return true;
      }
      // Check one level deeper for try-catch wrapping try-finally
      if (child instanceof CatchStatement || child instanceof SequenceStatement) {
        for (Statement grandchild : child.getStats()) {
          if (grandchild instanceof CatchAllStatement && ((CatchAllStatement) grandchild).isFinally()) {
            return true;
          }
        }
      }
    }
    return false;
  }

  /**
   * Check if the destination statement is the target of a TYPE_BREAK edge
   * whose source is strictly contained within the source statement. This
   * indicates that a control-flow path from inside the source reaches the
   * destination, so the destination is reachable even if the source's last
   * executed child ends with a non-regular exit (return/throw/break).
   *
   * This happens when an IfStatement has one branch that exits and another
   * that falls through: the fall-through edge becomes TYPE_BREAK during
   * collapseNodesToStatement, and the next sibling in the outer sequence
   * becomes a break target.
   */
  private static boolean hasBreakEdgeFromWithin(Statement source, Statement destination) {
    for (StatEdge pred : destination.getPredecessorEdges(StatEdge.TYPE_BREAK)) {
      if (source.containsStatementStrict(pred.getSource())) {
        return true;
      }
    }
    return false;
  }

  /**
   * Check if ALL execution paths through a statement end with a return or throw.
   * Unlike endsWithNonRegularExit (which checks edge-graph properties for
   * detecting unreachable-statement patterns), this method checks the actual
   * statement structure to determine if every code path exits.
   *
   * Used by the try-finally suppression check: a try-finally only makes
   * subsequent siblings unreachable if every path in the try body returns/throws.
   * For try-catch-finally, this means checking ALL catch handlers too.
   */
  private static boolean allPathsExit(Statement stat) {
    if (stat == null) {
      return false;
    }

    // Basic block: check if last exprent is a return or throw
    if (stat.getExprents() != null) {
      List<org.jetbrains.java.decompiler.modules.decompiler.exps.Exprent> exprents = stat.getExprents();
      if (!exprents.isEmpty()) {
        Object last = exprents.get(exprents.size() - 1);
        if (last instanceof org.jetbrains.java.decompiler.modules.decompiler.exps.ExitExprent) {
          return true;
        }
      }
      return false;
    }

    switch (stat.type) {
      case SEQUENCE:
        List<Statement> seqStats = stat.getStats();
        if (seqStats.isEmpty()) return false;
        return allPathsExit(seqStats.get(seqStats.size() - 1));

      case IF:
        IfStatement ifStat = (IfStatement) stat;
        if (ifStat.iftype == IfStatement.IFTYPE_IFELSE) {
          return allPathsExit(ifStat.getIfstat())
              && allPathsExit(ifStat.getElsestat());
        }
        return false;

      case TRY_CATCH:
        // All branches (try body + all catch handlers) must exit
        for (Statement sub : stat.getStats()) {
          if (!allPathsExit(sub)) {
            return false;
          }
        }
        return !stat.getStats().isEmpty();

      case CATCH_ALL:
        // For try-finally: the try body must exit on all paths
        // (the finally handler runs but doesn't change whether paths exit)
        return allPathsExit(stat.getFirst());

      case SWITCH:
        SwitchStatement swStat = (SwitchStatement) stat;
        List<Statement> caseStmts = swStat.getCaseStatements();
        if (caseStmts.isEmpty()) return false;
        for (Statement caseStat : caseStmts) {
          if (!allPathsExit(caseStat)) {
            return false;
          }
        }
        return true;

      case DO:
        DoStatement doStat = (DoStatement) stat;
        if (doStat.getLooptype() == DoStatement.Type.INFINITE) {
          return true;
        }
        return false;

      case SYNCHRONIZED:
        SynchronizedStatement synStat = (SynchronizedStatement) stat;
        return allPathsExit(synStat.getBody());

      default:
        return false;
    }
  }

  /**
   * Check if a finally handler ends with a return statement (not a throw).
   * Normal finally handlers re-throw the caught exception (ending with throw),
   * but a finally block that contains a return statement overrides all exits,
   * making code after the try-finally unreachable.
   */
  private static boolean handlerEndsWithReturn(Statement handler) {
    // For sequences, check the last child
    if (handler instanceof SequenceStatement) {
      VBStyleCollection<Statement, Integer> children = handler.getStats();
      if (!children.isEmpty()) {
        return handlerEndsWithReturn(children.getLast());
      }
    }

    if (handler.getExprents() != null && !handler.getExprents().isEmpty()) {
      Object lastExpr = handler.getExprents().get(handler.getExprents().size() - 1);
      if (lastExpr instanceof org.jetbrains.java.decompiler.modules.decompiler.exps.ExitExprent) {
        return ((org.jetbrains.java.decompiler.modules.decompiler.exps.ExitExprent) lastExpr).getExitType()
            == org.jetbrains.java.decompiler.modules.decompiler.exps.ExitExprent.Type.RETURN;
      }
    }

    return false;
  }

  @Override
  public Statement getSimpleCopy() {
    return new SequenceStatement();
  }
}
