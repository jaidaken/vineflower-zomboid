/*
 * Copyright 2000-2017 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
 */
package org.jetbrains.java.decompiler.modules.decompiler.exps;

import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.extern.IFernflowerLogger;
import org.jetbrains.java.decompiler.modules.decompiler.vars.CheckTypesResult;
import org.jetbrains.java.decompiler.struct.gen.CodeType;
import org.jetbrains.java.decompiler.struct.gen.TypeFamily;
import org.jetbrains.java.decompiler.struct.gen.VarType;
import org.jetbrains.java.decompiler.util.InterpreterUtil;
import org.jetbrains.java.decompiler.util.TextBuffer;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.List;
import java.util.Objects;

public class SwitchHeadExprent extends Exprent {

  private Exprent value;
  private List<List<Exprent>> caseValues = new ArrayList<>();

  public SwitchHeadExprent(Exprent value, BitSet bytecodeOffsets) {
    super(Type.SWITCH_HEAD);
    this.value = value;

    addBytecodeOffsets(bytecodeOffsets);
  }

  @Override
  public Exprent copy() {
    SwitchHeadExprent swExpr = new SwitchHeadExprent(value.copy(), bytecode);

    List<List<Exprent>> lstCaseValues = new ArrayList<>();
    for (List<Exprent> lst : caseValues) {
      lstCaseValues.add(new ArrayList<>(lst));
    }
    swExpr.setCaseValues(lstCaseValues);

    return swExpr;
  }

  @Override
  public VarType getExprType() {
    return value.getExprType();
  }

  @Override
  public CheckTypesResult checkExprTypeBounds() {
    CheckTypesResult result = new CheckTypesResult();

    // TODO: this surely can't be right with switch on enum and string?
    result.addMinTypeExprent(value, VarType.VARTYPE_BYTECHAR);
    result.addMaxTypeExprent(value, VarType.VARTYPE_INT);

    VarType valType = value.getExprType();
    for (List<Exprent> lst : caseValues) {
      for (Exprent expr : lst) {
        if (expr != null) {
          // TODO: refactor to PatternExprent
          VarType caseType = expr instanceof FunctionExprent && ((FunctionExprent) expr).getLstOperands().size() == 3
            ? ((FunctionExprent) expr).getLstOperands().get(1).getExprType()
            : expr.getExprType();
          if (!caseType.equals(valType)) {
            if (valType == null) {
              throw new IllegalStateException("Invalid switch case set: " + caseValues + " for selector of type " + value.getExprType());
            }
            // allow coercion of primitive -> boxes [see TestSwitchPatternMatching18]
            // e.g. `switch(o) { case 40 -> ...; case Integer i -> ...; }`
            // FIXME: still isn't right?
            VarType unboxed = VarType.UNBOXING_TYPES.get(valType);
            if (unboxed != null && unboxed.isSuperset(caseType)) {
              continue;
            }
            valType = VarType.getCommonSupertype(caseType, valType);
            if (valType != null) {
              result.addMinTypeExprent(value, valType);
            }
          }
        }
      }
    }

    return result;
  }

  @Override
  public List<Exprent> getAllExprents(List<Exprent> lst) {
    lst.add(value);
    return lst;
  }

  @Override
  public TextBuffer toJava(int indent) {
    TextBuffer valBuf = value.toJava(indent);
    // RTF: when the switch selector would be Object at compile time (from erased
    // generics on raw collections) but the switch uses LOOKUPSWITCH/TABLESWITCH
    // (which operates on int), insert an (int) cast.
    // The value's getExprType() may have been narrowed by checkExprTypeBounds to int,
    // but the RENDERED expression still returns Object from the raw method call.
    // Check the method descriptor directly.
    if (DecompilerContext.isRoundtripFidelity()) {
      boolean needsCast = false;
      Exprent innerValue = value;
      // Unwrap casts to get the actual expression
      while (innerValue instanceof FunctionExprent
          && ((FunctionExprent)innerValue).getFuncType() == FunctionExprent.FunctionType.CAST) {
        innerValue = ((FunctionExprent)innerValue).getLstOperands().get(0);
      }
      if (innerValue instanceof InvocationExprent) {
        String desc = ((InvocationExprent) innerValue).getStringDescriptor();
        if (desc != null && desc.endsWith(")Ljava/lang/Object;")) {
          needsCast = true;
        }
      }
      if (!needsCast && innerValue instanceof VarExprent) {
        VarExprent ve = (VarExprent) innerValue;
        if (ve.getLVT() != null && "java/lang/Object".equals(ve.getLVT().getVarType().value)) {
          needsCast = true;
        }
      }
      if (needsCast) {
        valBuf = valBuf.enclose("(int)", "");
      }
    }
    TextBuffer buf = valBuf.enclose("switch (", ")");
    buf.addStartBytecodeMapping(bytecode);
    return buf;
  }

  private boolean hasOnlyIntConstCaseValues() {
    for (List<Exprent> values : caseValues) {
      for (Exprent val : values) {
        if (val == null) continue;
        if (!(val instanceof ConstExprent)) return false;
        VarType ct = ((ConstExprent) val).getConstType();
        if (ct.typeFamily != TypeFamily.INTEGER && ct != VarType.VARTYPE_NULL) return false;
      }
    }
    return true;
  }

  @Override
  public void replaceExprent(Exprent oldExpr, Exprent newExpr) {
    if (oldExpr == value) {
      value = newExpr;
    }
  }

  @Override
  public boolean equals(Object o) {
    if (o == this) {
      return true;
    }

    if (!(o instanceof SwitchHeadExprent)) {
      return false;
    }

    SwitchHeadExprent sw = (SwitchHeadExprent)o;
    return InterpreterUtil.equalObjects(value, sw.getValue());
  }

  @Override
  public void getBytecodeRange(BitSet values) {
    if (caseValues != null && !caseValues.isEmpty()) {
      for (List<Exprent> l : caseValues) {
        if (l != null && !l.isEmpty()) {
          for (Exprent e : l) {
            if (e != null)
              e.getBytecodeRange(values);
          }
        }
      }
    }
    measureBytecode(values, value);
    measureBytecode(values);
  }

  public Exprent getValue() {
    return value;
  }

  public void setValue(Exprent value) {
    this.value = value;
  }

  public void setCaseValues(List<List<Exprent>> caseValues) {
    this.caseValues = caseValues;
  }
}
