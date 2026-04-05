/*
 * Copyright 2000-2017 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
 */
package org.jetbrains.java.decompiler.modules.decompiler.exps;

import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.modules.decompiler.exps.FunctionExprent.FunctionType;
import org.jetbrains.java.decompiler.modules.decompiler.sforms.SFormsConstructor;
import org.jetbrains.java.decompiler.modules.decompiler.sforms.VarMapHolder;
import org.jetbrains.java.decompiler.modules.decompiler.stats.Statement;
import org.jetbrains.java.decompiler.struct.gen.VarType;
import org.jetbrains.java.decompiler.util.InterpreterUtil;
import org.jetbrains.java.decompiler.util.collections.ListStack;
import org.jetbrains.java.decompiler.util.TextBuffer;

import java.util.BitSet;
import java.util.List;

public class IfExprent extends Exprent {
  public enum Type {
    // The order of these matters, see getNegative()
    EQ(FunctionType.EQ),
    NE(FunctionType.NE),
    LT(FunctionType.LT),
    GE(FunctionType.GE),
    GT(FunctionType.GT),
    LE(FunctionType.LE),
    NULL(FunctionType.EQ),
    NONNULL(FunctionType.NE),
    ICMPEQ(FunctionType.EQ),
    ICMPNE(FunctionType.NE),
    ICMPLT(FunctionType.LT),
    ICMPGE(FunctionType.GE),
    ICMPGT(FunctionType.GT),
    ICMPLE(FunctionType.LE),
    ACMPEQ(FunctionType.EQ),
    ACMPNE(FunctionType.NE),
    VALUE(null),
    ;

    private static final Type[] VALUES = values();

    final FunctionType functionType;

    Type(FunctionType functionType) {
      this.functionType = functionType;
    }

    public FunctionType getFunctionType() {
      return functionType;
    }

    public Type getNegative() {
      if (this == VALUE) throw new IllegalArgumentException();
      // All types except VALUE are paired up with their inverse,
      // the XOR selects the other item within that pair
      return VALUES[ordinal() ^ 1];
    }
  }

  private Exprent condition;
  // RTF: the original bytecode condition type (before VF's initial negation).
  // This is the negation of ifType passed to the constructor (since ExprProcessor
  // passes getNegative()). Used by post-passes to detect when the condition was
  // flipped from the original bytecode direction.
  private Type originalBytecodeType;

  // RTF: the raw bytecode opcode (e.g. Opcodes.IFNE = 154). Set once by
  // ExprProcessor at construction, never modified, never copied. Copies
  // get 0 which means "not from original bytecode". This field survives
  // all transformation passes because it is never touched by copy/negate.
  private int rawBytecodeOpcode;

  public IfExprent(Type ifType, ListStack<Exprent> stack, BitSet bytecodeOffsets) {
    this(ifType, stack, bytecodeOffsets, 0);
  }

  public IfExprent(Type ifType, ListStack<Exprent> stack, BitSet bytecodeOffsets, int rawOpcode) {
    this(null, bytecodeOffsets);
    // ifType is already the NEGATED form (ExprProcessor calls getNegative()).
    // The original bytecode type is the negation of ifType.
    this.originalBytecodeType = (ifType != Type.VALUE) ? ifType.getNegative() : null;
    this.rawBytecodeOpcode = rawOpcode;

    if (ifType.ordinal() <= Type.LE.ordinal()) {
      stack.push(new ConstExprent(0, true, null));
    }
    else if (ifType.ordinal() <= Type.NONNULL.ordinal()) {
      stack.push(new ConstExprent(VarType.VARTYPE_NULL, null, null));
    }

    condition = ifType.functionType == null ? stack.pop() : new FunctionExprent(ifType.functionType, stack, bytecodeOffsets);
  }

  public Type getOriginalBytecodeType() {
    return originalBytecodeType;
  }

  /**
   * RTF: returns the raw bytecode opcode (e.g. IFNE=154, IFEQ=153).
   * Returns 0 if this IfExprent was not constructed directly from bytecode
   * (i.e. it is a copy or was created by a transformation pass).
   */
  public int getRawBytecodeOpcode() {
    return rawBytecodeOpcode;
  }

  private IfExprent(Exprent condition, BitSet bytecodeOffsets) {
    super(Exprent.Type.IF);
    this.condition = condition;

    addBytecodeOffsets(bytecodeOffsets);
  }

  @Override
  public Exprent copy() {
    IfExprent copy = new IfExprent(condition.copy(), bytecode);
    copy.originalBytecodeType = this.originalBytecodeType;
    // rawBytecodeOpcode is an absolute fact ("the original bytecode was IFNE")
    // and its meaning does not change when the condition is transformed.
    // Unlike originalBytecodeType, which represents a comparison type that
    // gets reinterpreted by transformations, rawBytecodeOpcode is just the
    // raw JVM opcode integer. Safe to copy.
    copy.rawBytecodeOpcode = this.rawBytecodeOpcode;
    return copy;
  }

  @Override
  public List<Exprent> getAllExprents(List<Exprent> lst) {
    lst.add(condition);
    return lst;
  }

  @Override
  public TextBuffer toJava(int indent) {
    // The general context of if conditions is that they must always return booleans.
    // RTF: skip inference for simple comparisons (NE/EQ/LT/etc.) because it propagates
    // BOOLEAN to operands, changing const(0) type to BOOLEAN, which causes NE(var,0)
    // to simplify to bare var during rendering. Comparisons already return BOOLEAN.
    // Still run inference for compound conditions (&&, ||) and non-comparison expressions
    // because those need the type hint for correct rendering.
    boolean skipInference = false;
    if (DecompilerContext.isRoundtripFidelity()) {
      if (condition instanceof FunctionExprent) {
        FunctionExprent.FunctionType ft = ((FunctionExprent) condition).getFuncType();
        if (ft.ordinal() >= FunctionExprent.FunctionType.EQ.ordinal()
            && ft.ordinal() <= FunctionExprent.FunctionType.LE.ordinal()) {
          skipInference = true;
        }
      }
    }
    if (!skipInference) {
      condition.getInferredExprType(VarType.VARTYPE_BOOLEAN);
    }

    // RTF: if condition is a bare VarExprent with non-boolean type after all
    // simplification passes (variable merging changed boolean to int), wrap
    // in explicit "!= 0" for rendering only.
    Exprent renderCond = condition;
    if (DecompilerContext.isRoundtripFidelity() && condition instanceof VarExprent) {
      VarType ct = condition.getExprType();
      VarExprent condVar = (VarExprent) condition;
      boolean isDualTyped = condVar.getProcessor() != null
          && condVar.getProcessor().isDualTypedVar(condVar.getName());
      if ((ct != null && ct.type != org.jetbrains.java.decompiler.struct.gen.CodeType.BOOLEAN
           && ct.typeFamily == org.jetbrains.java.decompiler.struct.gen.TypeFamily.INTEGER)
          || isDualTyped) {
        renderCond = new FunctionExprent(FunctionExprent.FunctionType.NE,
          java.util.Arrays.asList(condition, new ConstExprent(VarType.VARTYPE_INT, 0, null)),
          condition.bytecode);
      }
    }

    TextBuffer buf = renderCond.toJava(indent);
    buf.pushNewlineGroup(indent, 1);
    buf.appendPossibleNewline();
    buf.enclose("if (", ")");
    buf.appendPossibleNewline("", true);
    buf.popNewlineGroup();
    buf.addStartBytecodeMapping(bytecode);
    return buf;
  }

  @Override
  public void replaceExprent(Exprent oldExpr, Exprent newExpr) {
    if (oldExpr == condition) {
      condition = newExpr;
    }
  }

  @Override
  public boolean equals(Object o) {
    if (o == this) return true;
    if (!(o instanceof IfExprent)) return false;

    IfExprent ie = (IfExprent)o;
    return InterpreterUtil.equalObjects(condition, ie.getCondition());
  }

  public IfExprent negateIf() {
    condition = new FunctionExprent(FunctionType.BOOL_NOT, condition, condition.bytecode);
    return this;
  }

  public Exprent getCondition() {
    return condition;
  }

  public void setCondition(Exprent condition) {
    this.condition = condition;
  }

  @Override
  public void getBytecodeRange(BitSet values) {
    measureBytecode(values, condition);
    measureBytecode(values);
  }

  @Override
  public void processSforms(SFormsConstructor sFormsConstructor, VarMapHolder varMaps, Statement stat, boolean calcLiveVars) {
    // EXPRENT_IF is a wrapper for the head exprent of an if statement.
    // Therefore, the map needs to stay split, unlike with most other exprents.
    this.getCondition().processSforms(sFormsConstructor, varMaps, stat, calcLiveVars);
  }
}
