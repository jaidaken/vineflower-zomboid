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
        break;
      }

      // RTF: a try-finally can make subsequent siblings unreachable in two ways:
      // 1. The finally handler itself returns, overriding any try-body completion.
      // 2. All paths in the try body return/throw, so the finally just cleans up
      //    and the method exits from within the try-finally.
      // For case 1, check if the handler ends with a return (not throw — throw
      // is normal re-throw behavior for finally handlers).
      // For case 2, check if the CatchAllStatement has no successor edges at all,
      // which means all execution paths exit internally.
      if (DecompilerContext.isRoundtripFidelity() && i < stats.size() - 1
          && st instanceof CatchAllStatement && ((CatchAllStatement) st).isFinally()) {
        CatchAllStatement cas = (CatchAllStatement) st;
        if (handlerEndsWithReturn(cas.getHandler())
            || cas.getSuccessorEdges(STATEDGE_DIRECT_ALL).isEmpty()) {
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
   */
  private static boolean endsWithNonRegularExit(Statement stat) {
    // Check the statement's own direct successor edges (same condition as jmpWrapper)
    List<StatEdge> succs = stat.getSuccessorEdges(STATEDGE_DIRECT_ALL);
    if (succs.size() == 1) {
      StatEdge edge = succs.get(0);
      if (edge.getType() != StatEdge.TYPE_REGULAR && edge.explicit) {
        return true;
      }
    }

    // A SwitchStatement with an explicit default case and no outgoing successor
    // edges: all execution paths exit via throw/return, so subsequent siblings
    // are unreachable.
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
        return true;
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

    return false;
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
