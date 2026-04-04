// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.modules.decompiler.stats;

import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.modules.decompiler.ExprProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.StatEdge;
import org.jetbrains.java.decompiler.modules.decompiler.exps.Exprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.FunctionExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.FunctionExprent.FunctionType;
import org.jetbrains.java.decompiler.modules.decompiler.exps.InvocationExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.Pattern;
import org.jetbrains.java.decompiler.modules.decompiler.exps.VarExprent;
import org.jetbrains.java.decompiler.code.CodeConstants;
import org.jetbrains.java.decompiler.struct.StructClass;
import org.jetbrains.java.decompiler.struct.gen.CodeType;
import org.jetbrains.java.decompiler.struct.gen.VarType;
import org.jetbrains.java.decompiler.struct.gen.generics.GenericClassDescriptor;
import org.jetbrains.java.decompiler.util.TextBuffer;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

// Loop statement
public class DoStatement extends Statement {
  public enum Type {
    INFINITE, DO_WHILE, WHILE, FOR, FOR_EACH
  }

  private Type looptype;

  private boolean rtfForceForEachVar = false;

  // RTF: preserved from the original .iterator() InvocationExprent before it's discarded
  // during for-each conversion in MergeHelper.matchForEach(). Used to emit the correct
  // cast type (matching the original invokevirtual/invokeinterface dispatch).
  private String rtfIteratorClassname = null;
  private InvocationExprent.InvocationType rtfIteratorInvocationType = null;

  private final List<Exprent> initExprent = new ArrayList<>();
  private final List<Exprent> conditionExprent = new ArrayList<>();
  private final List<Exprent> incExprent = new ArrayList<>();

  // *****************************************************************************
  // constructors
  // *****************************************************************************

  protected DoStatement() {
    super(StatementType.DO);
    looptype = Type.INFINITE;

    initExprent.add(null);
    conditionExprent.add(null);
    incExprent.add(null);
  }

  protected DoStatement(Statement head) {

    this();

    first = head;
    stats.addWithKey(first, first.id);

    // post is always null!
  }

  // *****************************************************************************
  // public methods
  // *****************************************************************************

  public static Statement isHead(Statement head) {

    if (head.getLastBasicType() == LastBasicType.GENERAL && !head.isMonitorEnter()) {

      // at most one outgoing edge
      StatEdge edge = null;
      List<StatEdge> lstSuccs = head.getSuccessorEdges(STATEDGE_DIRECT_ALL);
      if (!lstSuccs.isEmpty()) {
        edge = lstSuccs.get(0);
      }

      // regular loop
      if (edge != null && edge.getType() == StatEdge.TYPE_REGULAR && edge.getDestination() == head) {
        return new DoStatement(head);
      }

      // continues
      if (!(head instanceof DoStatement) && (edge == null || edge.getType() != StatEdge.TYPE_REGULAR) &&
          head.getContinueSet().contains(head.getBasichead())) {
        return new DoStatement(head);
      }
    }

    return null;
  }

  @Override
  public HashSet<Statement> buildContinueSet() {
    super.buildContinueSet();

    continueSet.remove(first.getBasichead());

    return continueSet;
  }

  @Override
  public TextBuffer toJava(int indent) {
    TextBuffer buf = new TextBuffer();

    buf.append(ExprProcessor.listToJava(varDefinitions, indent));

    if (isLabeled()) {
      buf.appendIndent(indent).append("label").append(this.id).append(":").appendLineSeparator();
    }

    switch (looptype) {
      case INFINITE:
        buf.appendIndent(indent).append("while (true) {").appendLineSeparator();
        buf.append(ExprProcessor.jmpWrapper(first, indent + 1, false));
        buf.appendIndent(indent).append("}").appendLineSeparator();
        break;
      case DO_WHILE:
        buf.appendIndent(indent).append("do {").appendLineSeparator();
        buf.append(ExprProcessor.jmpWrapper(first, indent + 1, false));
        buf.appendIndent(indent).append("} while (");
        buf.pushNewlineGroup(indent, 1);
        buf.appendPossibleNewline();
        buf.append(conditionExprent.get(0).toJava(indent));
        buf.appendPossibleNewline("", true);
        buf.popNewlineGroup();
        buf.append(");").appendLineSeparator();
        break;
      case WHILE:
        buf.appendIndent(indent).append("while (");
        buf.pushNewlineGroup(indent, 1);
        buf.appendPossibleNewline();
        buf.append(conditionExprent.get(0).toJava(indent));
        buf.appendPossibleNewline("", true);
        buf.popNewlineGroup();
        buf.append(") {").appendLineSeparator();
        buf.append(ExprProcessor.jmpWrapper(first, indent + 1, false));
        buf.appendIndent(indent).append("}").appendLineSeparator();
        break;
      case FOR:
        buf.appendIndent(indent);
        buf.pushNewlineGroup(indent, 1);
        buf.append("for (");
        if (initExprent.get(0) != null) {
          buf.append(initExprent.get(0).toJava(indent));
        }
        buf.append(";").appendPossibleNewline(" ")
          .append(conditionExprent.get(0).toJava(indent)).append(";").appendPossibleNewline(" ")
          .append(incExprent.get(0).toJava(indent))
          .appendPossibleNewline("", true);
        buf.popNewlineGroup();
        buf.append(") {").appendLineSeparator();
        buf.append(ExprProcessor.jmpWrapper(first, indent + 1, false));
        buf.appendIndent(indent).append("}").appendLineSeparator();
        break;
      case FOR_EACH:
        buf.appendIndent(indent).append("for (").append(initExprent.get(0).toJava(indent));
        incExprent.get(0).getInferredExprType(null); //TODO: Find a better then null? For now just calls it to clear casts if needed
        TextBuffer iterBuf = incExprent.get(0).toJava(indent);
        // RTF: when the for-each variable type is specific (narrowed from Object)
        // but the iterable is a raw collection, cast the iterable so javac accepts
        // the element type. Uses the original .iterator() receiver class (preserved
        // from MergeHelper) to match the original invokevirtual/invokeinterface dispatch.
        if (DecompilerContext.isRoundtripFidelity() && initExprent.get(0) instanceof VarExprent) {
          VarExprent feVar = (VarExprent) initExprent.get(0);
          VarType feType = feVar.getVarType();
          if (feType != null && feType.type == CodeType.OBJECT
              && !"java/lang/Object".equals(feType.value)
              && !feVar.isUseVar()) {
            VarType iterType = incExprent.get(0).getExprType();
            if (iterType.type == CodeType.OBJECT && iterType.arrayDim == 0) {
              // Use the inferred type if it's a generic type variable (e.g., E, T)
              // instead of the erased bound type (e.g., BaseScriptObject)
              VarType castElementType = feType;
              VarType inferredType = feVar.getInferredExprType(null);
              if (inferredType != null && inferredType.type == CodeType.GENVAR) {
                castElementType = inferredType;
              }
              String typeStr = ExprProcessor.getCastTypeName(castElementType);
              Exprent iterExpr = incExprent.get(0);
              if (iterExpr.getPrecedence() >= FunctionExprent.FunctionType.CAST.precedence) {
                iterBuf = iterBuf.encloseWithParens();
              }
              // Use the original iterator receiver class instead of always Iterable.
              // This preserves the original dispatch: invokevirtual for concrete classes
              // (ArrayList, etc.) and invokeinterface for interfaces (Iterable, List, etc.)
              String castClass = "Iterable";
              boolean skipCast = false;
              if (rtfIteratorClassname != null) {
                // Check if the iterator class accepts type parameters.
                // Non-generic classes (e.g., EdgeRing extends ArrayList<Edge>) don't
                // take type parameters, so casting to (EdgeRing<Edge>) would be invalid.
                // For these classes, the element type is already inferrable from the
                // generic superclass, so skip the cast entirely.
                boolean classIsGeneric = true;
                StructClass iterStruct = DecompilerContext.getStructContext() != null
                    ? DecompilerContext.getStructContext().getClass(rtfIteratorClassname) : null;
                if (iterStruct != null) {
                  GenericClassDescriptor sig = iterStruct.getSignature();
                  if (sig != null && sig.fparameters.isEmpty()) {
                    // Class has a generic signature but no type parameters (e.g., EdgeRing extends ArrayList<Edge>)
                    // Element type is inferrable from the class hierarchy - skip the cast
                    skipCast = true;
                    classIsGeneric = false;
                  } else if (sig == null) {
                    // No generic signature at all - check if it's a well-known generic class
                    // (library classes like ArrayList may not have StructClass entries)
                    classIsGeneric = true;
                  }
                }
                if (classIsGeneric) {
                  castClass = ExprProcessor.getCastTypeName(new VarType(rtfIteratorClassname, true));
                }
              }
              if (!skipCast) {
                iterBuf = iterBuf.enclose("(" + castClass + "<" + typeStr + ">)(" + castClass + "<?>)", "");
              }
            }
          }
        }
        buf.append(" : ").append(iterBuf).append(") {").appendLineSeparator();
        buf.append(ExprProcessor.jmpWrapper(first, indent + 1, true));
        buf.appendIndent(indent).append("}").appendLineSeparator();
    }

    return buf;
  }

  @Override
  public List<Object> getSequentialObjects() {

    List<Object> lst = new ArrayList<>();

    switch (looptype) {
      case FOR:
        if (getInitExprent() != null) {
          lst.add(getInitExprent());
        }
      case WHILE:
        lst.add(getConditionExprent());
        break;
      case FOR_EACH:
        lst.add(getInitExprent());
        lst.add(getIncExprent());
    }

    lst.add(first);

    switch (looptype) {
      case DO_WHILE:
        lst.add(getConditionExprent());
        break;
      case FOR:
        lst.add(getIncExprent());
    }

    return lst;
  }

  @Override
  public void replaceExprent(Exprent oldexpr, Exprent newexpr) {
    if (initExprent.get(0) == oldexpr) {
      initExprent.set(0, newexpr);
    }
    if (conditionExprent.get(0) == oldexpr) {
      conditionExprent.set(0, newexpr);
    }
    if (incExprent.get(0) == oldexpr) {
      incExprent.set(0, newexpr);
    }
  }

  @Override
  public List<VarExprent> getImplicitlyDefinedVars() {
    List<VarExprent> vars = new ArrayList<>();

    // Impossible in foreach loops, and quit if condition doesn't exist
    if (looptype == Type.FOR_EACH || getConditionExprent() == null) {
      return null;
    }

    List<Exprent> conditionList = getConditionExprent().getAllExprents(true, true);

    for (Exprent condition : conditionList) {
      if (condition instanceof FunctionExprent func) {

        // Pattern match variable is implicitly defined
        if (func.getFuncType() == FunctionType.INSTANCEOF && func.getLstOperands().size() > 2) {
          vars.addAll(((Pattern) func.getLstOperands().get(2)).getPatternVars());
        }
      }
    }

    return vars;
  }

  @Override
  public boolean hasBasicSuccEdge() {
    return looptype != Type.INFINITE;
  }

  @Override
  public Statement getSimpleCopy() {
    return new DoStatement();
  }

  // *****************************************************************************
  // getter and setter methods
  // *****************************************************************************

  public List<Exprent> getInitExprentList() {
    return initExprent;
  }

  public List<Exprent> getConditionExprentList() {
    return conditionExprent;
  }

  public List<Exprent> getIncExprentList() {
    return incExprent;
  }

  public Exprent getConditionExprent() {
    return conditionExprent.get(0);
  }

  public void setConditionExprent(Exprent conditionExprent) {
    this.conditionExprent.set(0, conditionExprent);
  }

  public Exprent getIncExprent() {
    return incExprent.get(0);
  }

  public void setIncExprent(Exprent incExprent) {
    this.incExprent.set(0, incExprent);
  }

  public Exprent getInitExprent() {
    return initExprent.get(0);
  }

  public void setInitExprent(Exprent initExprent) {
    this.initExprent.set(0, initExprent);
  }

  public Type getLooptype() {
    return looptype;
  }

  public void setLooptype(Type looptype) {
    this.looptype = looptype;
  }

  public void setRtfForceForEachVar(boolean val) {
    this.rtfForceForEachVar = val;
  }

  public String getRtfIteratorClassname() {
    return rtfIteratorClassname;
  }

  public void setRtfIteratorClassname(String rtfIteratorClassname) {
    this.rtfIteratorClassname = rtfIteratorClassname;
  }

  public InvocationExprent.InvocationType getRtfIteratorInvocationType() {
    return rtfIteratorInvocationType;
  }

  public void setRtfIteratorInvocationType(InvocationExprent.InvocationType rtfIteratorInvocationType) {
    this.rtfIteratorInvocationType = rtfIteratorInvocationType;
  }
}
