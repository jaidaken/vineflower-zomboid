// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.modules.decompiler.stats;

import org.jetbrains.java.decompiler.code.CodeConstants;
import org.jetbrains.java.decompiler.code.cfg.BasicBlock;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.collectors.CounterContainer;
import org.jetbrains.java.decompiler.main.extern.IFernflowerPreferences;
import org.jetbrains.java.decompiler.modules.decompiler.ClasspathHelper;
import org.jetbrains.java.decompiler.modules.decompiler.DecHelper;
import org.jetbrains.java.decompiler.modules.decompiler.ExprProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.StatEdge;
import org.jetbrains.java.decompiler.modules.decompiler.exps.AssignmentExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.Exprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.InvocationExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.VarExprent;
import org.jetbrains.java.decompiler.struct.gen.CodeType;
import org.jetbrains.java.decompiler.struct.gen.VarType;
import org.jetbrains.java.decompiler.util.TextBuffer;

import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

public class CatchStatement extends Statement {
  private final List<List<String>> exctstrings = new ArrayList<>();
  private final List<VarExprent> vars = new ArrayList<>();
  private final List<Exprent> resources = new ArrayList<>();

  // *****************************************************************************
  // constructors
  // *****************************************************************************

  protected CatchStatement() {
    super(StatementType.TRY_CATCH);
  }

  protected CatchStatement(Statement head, Statement next, Set<Statement> setHandlers) {
    this();

    first = head;
    stats.addWithKey(first, first.id);

    for (StatEdge edge : head.getSuccessorEdges(StatEdge.TYPE_EXCEPTION)) {
      Statement stat = edge.getDestination();

      if (setHandlers.contains(stat)) {
        stats.addWithKey(stat, stat.id);
        exctstrings.add(new ArrayList<>(edge.getExceptions()));
        
        vars.add(new VarExprent(DecompilerContext.getCounterContainer().getCounterAndIncrement(CounterContainer.VAR_COUNTER),
                                new VarType(CodeType.OBJECT, 0, edge.getExceptions().get(0)),
                                // FIXME: for now simply the first type. Should get the first common superclass when possible.
                                DecompilerContext.getVarProcessor()));
      }
    }

    if (next != null) {
      post = next;
    }
  }

  // *****************************************************************************
  // public methods
  // *****************************************************************************

  public static Statement isHead(Statement head) {
    if (head.getLastBasicType() != LastBasicType.GENERAL) {
      return null;
    }

    Set<Statement> setHandlers = DecHelper.getUniquePredExceptions(head);
    if (!setHandlers.isEmpty()) {
      int hnextcount = 0; // either no statements with connection to next, or more than 1

      Statement next = null;
      List<StatEdge> lstHeadSuccs = head.getSuccessorEdges(STATEDGE_DIRECT_ALL);
      if (!lstHeadSuccs.isEmpty() && lstHeadSuccs.get(0).getType() == StatEdge.TYPE_REGULAR) {
        next = lstHeadSuccs.get(0).getDestination();
        hnextcount = 2;
      }

      for (StatEdge edge : head.getSuccessorEdges(StatEdge.TYPE_EXCEPTION)) {
        Statement stat = edge.getDestination();

        boolean handlerok = true;

        if (edge.getExceptions() != null && setHandlers.contains(stat)) {
          if (stat.getLastBasicType() != LastBasicType.GENERAL) {
            handlerok = false;
          } else {
            List<StatEdge> lstStatSuccs = stat.getSuccessorEdges(STATEDGE_DIRECT_ALL);
            if (!lstStatSuccs.isEmpty() && lstStatSuccs.get(0).getType() == StatEdge.TYPE_REGULAR) {

              Statement statn = lstStatSuccs.get(0).getDestination();

              if (next == null) {
                next = statn;
              } else if (next != statn) {
                handlerok = false;
              }

              if (handlerok) {
                hnextcount++;
              }
            }
          }
        } else {
          handlerok = false;
        }

        if (!handlerok) {
          setHandlers.remove(stat);
        }
      }

      if (hnextcount != 1 && !setHandlers.isEmpty()) {
        List<Statement> lst = new ArrayList<>();
        lst.add(head);
        lst.addAll(setHandlers);

        for (Statement st : lst) {
          if (st.isMonitorEnter()) {
            return null;
          }
        }

        if (DecHelper.invalidHeadMerge(head)) {
          return null;
        }

        if (DecHelper.checkStatementExceptions(lst)) {
          return new CatchStatement(head, next, setHandlers);
        }
      }
    }
    return null;
  }

  @Override
  public TextBuffer toJava(int indent) {
    TextBuffer buf = new TextBuffer();

    buf.append(ExprProcessor.listToJava(varDefinitions, indent));

    if (isLabeled()) {
      buf.appendIndent(indent).append("label").append(this.id).append(":").appendLineSeparator();
    }

    if (resources.isEmpty()) {
      buf.appendIndent(indent).append("try {").appendLineSeparator();
    }
    else {
      buf.appendIndent(indent).append("try (");

      if (resources.size() > 1) {
        buf.appendLineSeparator();
        buf.append(ExprProcessor.listToJava(resources, indent + 1));
        buf.appendIndent(indent);
      }
      else {
        buf.append(resources.get(0).toJava(indent + 1));
      }
      buf.append(") {").appendLineSeparator();
    }

    buf.append(ExprProcessor.jmpWrapper(first, indent + 1, true));
    buf.appendIndent(indent).append("}");

    for (int i = 1; i < stats.size(); i++) {
      Statement stat = stats.get(i);
      // map first instruction storing the exception to the catch statement
      BasicBlock block = stat.getBasichead().getBlock();
      if (!block.getSeq().isEmpty() && block.getInstruction(0).opcode == CodeConstants.opc_astore) {
        Integer offset = block.getOldOffset(0);
        if (offset > -1) buf.addBytecodeMapping(offset);
      }

      buf.append(" catch (");

      List<String> exception_types = exctstrings.get(i - 1);
      // RTF: widen checked exceptions that the try body cannot throw.
      // The bytecode exception table may list specific exceptions (e.g.,
      // CloneNotSupportedException) even though the source used a broader
      // catch (Exception). Javac rejects catch clauses for checked exceptions
      // not thrown by the try body.
      if (DecompilerContext.isRoundtripFidelity() && exception_types.size() == 1) {
        String excType = exception_types.get(0);
        boolean shouldWiden = false;
        if ("java/lang/CloneNotSupportedException".equals(excType)
            || "java/lang/ReflectiveOperationException".equals(excType)) {
          shouldWiden = true;
        } else if ("java/lang/InterruptedException".equals(excType)) {
          // Only widen InterruptedException if the try body has no methods that throw it.
          // When the try body calls Thread.sleep(), Object.wait(), etc., the original
          // catch type is valid and should be preserved.
          shouldWiden = !tryBodyCanThrowException(first, "java.lang.InterruptedException");
        }
        if (shouldWiden) {
          // Check if another catch clause already handles Exception
          boolean hasExceptionCatch = false;
          for (int j = 0; j < exctstrings.size(); j++) {
            if (j != i - 1 && exctstrings.get(j).contains("java/lang/Exception")) {
              hasExceptionCatch = true;
              break;
            }
          }
          if (!hasExceptionCatch) {
            exception_types = new java.util.ArrayList<>(exception_types);
            exception_types.set(0, "java/lang/Exception");
            VarExprent catchVar = vars.get(i - 1);
            catchVar.setVarType(new VarType(CodeType.OBJECT, 0, "java/lang/Exception"));
          }
        }
      }
      if (exception_types.size() > 1) { // multi-catch, Java 7 style
        for (int exc_index = 1; exc_index < exception_types.size(); ++exc_index) {
          VarType exc_type = new VarType(CodeType.OBJECT, 0, exception_types.get(exc_index));
          String exc_type_name = ExprProcessor.getCastTypeName(exc_type);

          buf.append(exc_type_name).append(" | ");
        }
      }
      buf.append(vars.get(i - 1).toJava(indent));
      buf.append(") {").appendLineSeparator();
      buf.append(ExprProcessor.jmpWrapper(stat, indent + 1, false)).appendIndent(indent)
        .append("}");
    }
    buf.appendLineSeparator();

    return buf;
  }

  /**
   * Checks whether any method invocation in the given statement (recursively)
   * declares the specified exception in its throws clause.
   * Uses Java reflection to resolve method signatures, which works for JDK
   * classes like Thread.sleep(), Object.wait(), etc.
   *
   * @param statement the statement tree to search (typically the try body)
   * @param exceptionClassName the fully-qualified exception class name using dots (e.g. "java.lang.InterruptedException")
   * @return true if at least one method call declares the given exception
   */
  private static boolean tryBodyCanThrowException(Statement statement, String exceptionClassName) {
    Class<?> targetException;
    try {
      targetException = Class.forName(exceptionClassName);
    } catch (ClassNotFoundException e) {
      return false;
    }

    // Walk the statement tree iteratively to collect all exprents
    LinkedList<Statement> stmtQueue = new LinkedList<>();
    stmtQueue.add(statement);

    while (!stmtQueue.isEmpty()) {
      Statement stmt = stmtQueue.removeFirst();

      List<Exprent> exprents = stmt.getExprents();
      if (exprents != null) {
        for (Exprent expr : exprents) {
          if (exprContainsThrowingInvocation(expr, targetException)) {
            return true;
          }
        }
      }

      // Add sub-statements for recursive traversal
      for (Statement sub : stmt.getStats()) {
        stmtQueue.add(sub);
      }
    }

    return false;
  }

  /**
   * Checks whether the given exprent (or any nested exprent) is an InvocationExprent
   * whose resolved method declares the target exception type.
   */
  private static boolean exprContainsThrowingInvocation(Exprent expr, Class<?> targetException) {
    // Check this expression and all nested expressions
    List<Exprent> allExprents = expr.getAllExprents(true, true);
    for (Exprent e : allExprents) {
      if (e.type == Exprent.Type.INVOCATION) {
        InvocationExprent invoc = (InvocationExprent) e;
        Method method = ClasspathHelper.findMethod(invoc.getClassname(), invoc.getName(), invoc.getDescriptor());
        if (method != null) {
          for (Class<?> exc : method.getExceptionTypes()) {
            if (exc.isAssignableFrom(targetException) || targetException.isAssignableFrom(exc)) {
              return true;
            }
          }
        }
      }
    }
    return false;
  }

  public List<Object> getSequentialObjects() {

    List<Object> lst = new ArrayList<>(resources);
    lst.addAll(stats);
    lst.addAll(vars);

    return lst;
  }

  @Override
  public Statement getSimpleCopy() {
    CatchStatement cs = new CatchStatement();

    for (List<String> exc : this.exctstrings) {
      cs.exctstrings.add(new ArrayList<>(exc));
      cs.vars.add(new VarExprent(DecompilerContext.getCounterContainer().getCounterAndIncrement(CounterContainer.VAR_COUNTER),
                                 new VarType(CodeType.OBJECT, 0, exc.get(0)),
                                 DecompilerContext.getVarProcessor()));
    }

    return cs;
  }

  public void getOffset(BitSet values) {
    super.getOffset(values);

    for (Exprent exp : this.getResources()) {
      exp.getBytecodeRange(values);
    }
  }

  // *****************************************************************************
  // getter and setter methods
  // *****************************************************************************

  public List<List<String>> getExctStrings() {
    return exctstrings;
  }

  public List<VarExprent> getVars() {
    return vars;
  }

  public List<Exprent> getResources() {
    return resources;
  }

  @Override
  public List<VarExprent> getImplicitlyDefinedVars() {
    List<VarExprent> vars = new ArrayList<>(getVars());

    // resource vars must also be included
    for (Exprent exp : getResources()) {
      vars.add((VarExprent)((AssignmentExprent)exp).getLeft());
    }

    return vars;
  }
}