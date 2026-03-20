/*
 * Copyright 2000-2017 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
 */
package org.jetbrains.java.decompiler.modules.decompiler.exps;

import org.jetbrains.java.decompiler.code.CodeConstants;
import org.jetbrains.java.decompiler.main.ClassesProcessor.ClassNode;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.extern.IFernflowerPreferences;
import org.jetbrains.java.decompiler.main.rels.MethodWrapper;
import org.jetbrains.java.decompiler.modules.decompiler.ExprProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.sforms.SFormsConstructor;
import org.jetbrains.java.decompiler.modules.decompiler.sforms.VarMapHolder;
import org.jetbrains.java.decompiler.modules.decompiler.stats.Statement;
import org.jetbrains.java.decompiler.modules.decompiler.vars.CheckTypesResult;
import org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair;
import org.jetbrains.java.decompiler.struct.StructField;
import org.jetbrains.java.decompiler.struct.StructMethod;
import org.jetbrains.java.decompiler.struct.gen.CodeType;
import org.jetbrains.java.decompiler.struct.gen.VarType;
import org.jetbrains.java.decompiler.struct.gen.generics.GenericClassDescriptor;
import org.jetbrains.java.decompiler.struct.gen.generics.GenericMethodDescriptor;
import org.jetbrains.java.decompiler.struct.gen.generics.GenericType;
import org.jetbrains.java.decompiler.util.InterpreterUtil;
import org.jetbrains.java.decompiler.util.TextBuffer;
import org.jetbrains.java.decompiler.util.collections.SFormsFastMapDirect;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.List;
import java.util.Map;

public class AssignmentExprent extends Exprent {
  private Exprent left;
  private Exprent right;
  private FunctionExprent.FunctionType condType = null;

  public AssignmentExprent(Exprent left, Exprent right, BitSet bytecodeOffsets) {
    super(Type.ASSIGNMENT);
    this.left = left;
    this.right = right;

    addBytecodeOffsets(bytecodeOffsets);
  }

  public AssignmentExprent(Exprent left, Exprent right, FunctionExprent.FunctionType condType, BitSet bytecodeOffsets) {
    this(left, right, bytecodeOffsets);
    this.condType = condType;
  }

  @Override
  public VarType getExprType() {
    // Union together types
    VarType rType = VarType.getCommonSupertype(left.getExprType(), right.getExprType());
    // TODO: maybe there's a better default for null
    return rType == null ? left.getExprType() : rType;
  }

  @Override
  public VarType getInferredExprType(VarType upperBounds) {
    return left.getInferredExprType(upperBounds);
  }

  @Override
  public CheckTypesResult checkExprTypeBounds() {
    CheckTypesResult result = new CheckTypesResult();

    VarType typeLeft = left.getExprType();
    // RTF: use getInferredExprType for RHS to capture generic return types
    // from method signatures (e.g., Files.walk() -> Stream<Path>).
    VarType typeRight = DecompilerContext.isRoundtripFidelity()
        ? right.getInferredExprType(null) : right.getExprType();
    if (typeRight == null) typeRight = right.getExprType();

    if (typeLeft.typeFamily.isGreater(typeRight.typeFamily)) {
      result.addMinTypeExprent(right, VarType.getMinTypeInFamily(typeLeft.typeFamily));
    } else if (typeLeft.typeFamily.isLesser(typeRight.typeFamily)) {
      result.addMinTypeExprent(left, typeRight);
    }
    else {
      result.addMinTypeExprent(left, VarType.getCommonSupertype(typeLeft, typeRight));
    }

    return result;
  }

  @Override
  public List<Exprent> getAllExprents(List<Exprent> lst) {
    lst.add(left);
    lst.add(right);
    return lst;
  }

  @Override
  public Exprent copy() {
    return new AssignmentExprent(left.copy(), right.copy(), condType, bytecode);
  }

  @Override
  public int getPrecedence() {
    return 13;
  }

  @Override
  public TextBuffer toJava(int indent) {
    VarType leftType = left.getInferredExprType(null);

    boolean fieldInClassInit = false, hiddenField = false;
    if (left instanceof FieldExprent) { // first assignment to a final field. Field name without "this" in front of it
      FieldExprent field = (FieldExprent) left;
      ClassNode node = ((ClassNode) DecompilerContext.getContextProperty(DecompilerContext.CURRENT_CLASS_NODE));
      if (node != null) {
        StructField fd = node.classStruct.getField(field.getName(), field.getDescriptor().descriptorString);
        if (fd != null) {
          if (field.isStatic() && fd.hasModifier(CodeConstants.ACC_FINAL)) {
            fieldInClassInit = true;
          }
          if (node.getWrapper() != null && node.getWrapper().getHiddenMembers().contains(InterpreterUtil.makeUniqueKey(fd.getName(), fd.getDescriptor()))) {
            hiddenField = true;
          }
        }
      }
    }

    if (hiddenField) {
      return new TextBuffer();
    }

    TextBuffer buffer = new TextBuffer();

    if (fieldInClassInit) {
      FieldExprent field = (FieldExprent) left;
      buffer.appendField(field.getName(), false, field.getClassname(), field.getName(), field.getDescriptor());
    } else {
      buffer.append(left.toJava(indent));
    }

    if (right instanceof ConstExprent) {
      ((ConstExprent) right).adjustConstType(leftType);
    }

    this.optimizeCastForAssign();

    // RTF: re-enable narrowing casts (I2B/I2C/I2S) that were suppressed during processing.
    // Without this, "byte0 = byte0 + expr" loses its (byte) cast, causing lossy conversion errors.
    if (DecompilerContext.isRoundtripFidelity() && condType == null && right instanceof FunctionExprent) {
      FunctionExprent func = (FunctionExprent) right;
      FunctionExprent.FunctionType ft = func.getFuncType();
      if ((ft == FunctionExprent.FunctionType.I2B || ft == FunctionExprent.FunctionType.I2C || ft == FunctionExprent.FunctionType.I2S)
          && !func.doesCast()) {
        func.setNeedsCast(true);
      }
    }

    // RTF: track if we need to force a narrowing cast before the RHS.
    // When the I2B/I2C/I2S cast was removed during stack variable simplification,
    // the RHS is just an arithmetic expression without a cast wrapper. Java promotes
    // byte/short/char to int for arithmetic, so we must add an explicit narrowing cast.
    // We check both the declared type (from LVT/definition) and the inferred type.
    boolean forceNarrowingCast = false;
    VarType narrowCastType = null;
    if (DecompilerContext.isRoundtripFidelity() && condType == null
        && left instanceof VarExprent && right instanceof FunctionExprent) {
      VarExprent leftVar = (VarExprent) left;
      // Check both the inferred type and the definition type for narrowness
      VarType declaredType = leftVar.getDefinitionVarType();
      boolean lhsNarrow = declaredType.type == CodeType.BYTE || declaredType.type == CodeType.SHORT
          || declaredType.type == CodeType.CHAR || declaredType.type == CodeType.BYTECHAR
          || declaredType.type == CodeType.SHORTCHAR;
      if (!lhsNarrow) {
        // Fallback: check the inferred type as well
        VarType inferredType = leftVar.getExprType();
        lhsNarrow = inferredType.type == CodeType.BYTE || inferredType.type == CodeType.SHORT
            || inferredType.type == CodeType.CHAR || inferredType.type == CodeType.BYTECHAR
            || inferredType.type == CodeType.SHORTCHAR;
        if (lhsNarrow) {
          declaredType = inferredType;
        }
      }
      if (!lhsNarrow) {
        // Last resort: check the rendered variable name prefix.
        // The variable renaming plugin generates names like byte0, short0, char0
        // based on the LVT descriptor, even when the type has been widened to int.
        String varName = leftVar.getName();
        if (varName != null) {
          if (varName.startsWith("byte")) {
            lhsNarrow = true;
            declaredType = VarType.VARTYPE_BYTE;
          } else if (varName.startsWith("short")) {
            lhsNarrow = true;
            declaredType = VarType.VARTYPE_SHORT;
          } else if (varName.startsWith("char")) {
            lhsNarrow = true;
            declaredType = VarType.VARTYPE_CHAR;
          }
        }
      }
      if (lhsNarrow) {
        FunctionExprent func = (FunctionExprent) right;
        FunctionExprent.FunctionType ft = func.getFuncType();
        boolean isArithmetic = ft == FunctionExprent.FunctionType.ADD || ft == FunctionExprent.FunctionType.SUB
            || ft == FunctionExprent.FunctionType.MUL || ft == FunctionExprent.FunctionType.DIV
            || ft == FunctionExprent.FunctionType.REM
            || ft == FunctionExprent.FunctionType.AND || ft == FunctionExprent.FunctionType.OR
            || ft == FunctionExprent.FunctionType.XOR
            || ft == FunctionExprent.FunctionType.SHL || ft == FunctionExprent.FunctionType.SHR
            || ft == FunctionExprent.FunctionType.USHR;
        if (isArithmetic) {
          // Verify the RHS actually produces a wider type (int/long)
          VarType rhsType = right.getExprType();
          boolean rhsWider = rhsType.type == CodeType.INT || rhsType.type == CodeType.LONG;
          if (rhsWider) {
            forceNarrowingCast = true;
            narrowCastType = declaredType;
          }
        }
      }
    }

    if (condType == null) {
      buffer.append(" = ");

      if (forceNarrowingCast) {
        // Directly emit the narrowing cast and RHS without going through getCastedExprent,
        // which may not detect the need due to type inference widening the LHS type.
        buffer.append('(').appendCastTypeName(narrowCastType).append(')');
        buffer.append('(');
        buffer.append(right.toJava(indent));
        buffer.append(')');
      } else {
        // We must lock the collector: this prevents the retrieval of the cast type name to impact the import list.
        // This is fine as we're only using the cast type name to ensure that it's not the unrepresentable type.
        String castName;
        try (var lock = DecompilerContext.getImportCollector().lock()) {
          castName = ExprProcessor.getCastTypeName(leftType);
        }

        if (castName.equals(ExprProcessor.UNREPRESENTABLE_TYPE_STRING)) {
          // Unrepresentable, go ahead and just put the type on the right. The lhs (if a variable) should know about its type and change itself to "var" accordingly.
          buffer.append(right.toJava(indent));
        } else {
          // Cast with the left type
          ExprProcessor.getCastedExprent(right, leftType, buffer, indent, ExprProcessor.NullCastType.DONT_CAST_AT_ALL, false, false, false);

          // RTF: getCastedExprent uses getInferredExprType which may return a
          // specific type (Counter, int) even though the Java source shows Object
          // (from raw collection method). When the RHS is an InvocationExprent
          // whose DESCRIPTOR returns Object but the LHS is specific, the assignment
          // will fail at compile time. Detect this and re-render with explicit cast.
          if (DecompilerContext.isRoundtripFidelity()) {
            Exprent rawRight = right;
            // Unwrap function casts to find the underlying invocation
            while (rawRight instanceof FunctionExprent
                && ((FunctionExprent)rawRight).getFuncType() == FunctionExprent.FunctionType.CAST) {
              rawRight = ((FunctionExprent)rawRight).getLstOperands().get(0);
            }
            if (rawRight instanceof InvocationExprent) {
              InvocationExprent rightInv = (InvocationExprent) rawRight;
              String desc = rightInv.getStringDescriptor();
              if (desc != null && desc.endsWith(")Ljava/lang/Object;")
                  && leftType != null && !"java/lang/Object".equals(leftType.value)
                  && leftType.type != CodeType.NULL && leftType.type != CodeType.UNKNOWN
                  && leftType.type != CodeType.GENVAR
                  && !rightInv.isUnboxingCall() && !rightInv.isBoxingCall()) {
                // Check if the buffer already has a cast after the "= "
                String rendered = buffer.toString();
                int eqIdx = rendered.lastIndexOf("= ");
                if (eqIdx >= 0) {
                  String afterEq = rendered.substring(eqIdx + 2).trim();
                  if (!afterEq.startsWith("(")) {
                    // Re-render with explicit cast
                    buffer.setLength(eqIdx + 2);
                    buffer.append("(").appendCastTypeName(leftType).append(")");
                    buffer.append(right.toJava(indent));
                  }
                }
              }
            }
          }
        }
      }
    } else {
      buffer.append(" ").append(condType.operator).append("= ");
      buffer.append(right.toJava(indent));
    }

    buffer.addStartBytecodeMapping(bytecode);

    if (this.left instanceof VarExprent && DecompilerContext.getOption(IFernflowerPreferences.DECOMPILER_COMMENTS)) {
      VarExprent varLeft = (VarExprent) this.left;

      if (varLeft.isDefinition() && varLeft.getProcessor() != null) {
        if (varLeft.getProcessor().getSyntheticSemaphores().contains(varLeft.getIndex())) {
          buffer.append(" /* VF: Semaphore variable */");
        }
      }
    }

    return buffer;
  }

  // E var = (T)expr; -> E var = (E)expr;
  // when E extends T & A
  private void optimizeCastForAssign() {
    if (!(this.right instanceof FunctionExprent)) {
      return;
    }

    FunctionExprent func = (FunctionExprent) this.right;

    if (func.getFuncType() != FunctionExprent.FunctionType.CAST) {
      return;
    }

    Exprent cast = func.getLstOperands().get(1);

    // Fix for Object[] arr = (Object[])o; where is o is of type Object
    if (!func.doesCast() && this.left instanceof VarExprent) {
      // Same logic as FunctionExprent#getInferredExprType
      if (DecompilerContext.getStructContext().instanceOf(this.right.getExprType().value, cast.getExprType().value)) {
        Exprent castVal = func.getLstOperands().get(0);

        if (this.left.getExprType().arrayDim > castVal.getExprType().arrayDim) {
          func.setNeedsCast(true);
          return;
        }
      }
    }

    VarType leftType = this.left.getInferredExprType(null);

    if (!(leftType instanceof GenericType)) {
      return;
    }

    MethodWrapper method = (MethodWrapper) DecompilerContext.getContextProperty(DecompilerContext.CURRENT_METHOD_WRAPPER);
    if (method == null) {
      return;
    }

    StructMethod mt = method.methodStruct;
    GenericMethodDescriptor descriptor = mt.getSignature();


    if (descriptor == null || descriptor.typeParameters.isEmpty()) {
      return;
    }

    List<String> params = descriptor.typeParameters;
    int index = params.indexOf(leftType.value);
    if (index == -1) {
      return;
    }

    List<List<VarType>> bounds = descriptor.typeParameterBounds;

    List<VarType> types = bounds.get(index);

    GenericClassDescriptor classDescriptor = method.classStruct.getSignature();
    if (classDescriptor != null) {
      for (VarType type : new ArrayList<>(types)) {
        int idex = classDescriptor.fparameters.indexOf(type.value);

        if (idex != -1) {
          types.addAll(classDescriptor.fbounds.get(idex));
        }
      }
    }

    VarType rightType = cast.getInferredExprType(leftType);

    // Check if type bound includes the type that we are attempting to cast to
    boolean didReset = false;
    for (VarType type : types) {
      if (rightType.value.equals(type.value)) {
        ((ConstExprent)cast).setConstType(leftType);
        didReset = true;
      }
    }

    if (didReset) {
      // Reset cast state
      func.getInferredExprType(null);
    }
  }

  @Override
  public void replaceExprent(Exprent oldExpr, Exprent newExpr) {
    if (oldExpr == left) {
      left = newExpr;
    }
    if (oldExpr == right) {
      right = newExpr;
    }
  }

  @Override
  public boolean equals(Object o) {
    if (o == this) return true;
    if (!(o instanceof AssignmentExprent)) return false;

    AssignmentExprent as = (AssignmentExprent)o;
    return InterpreterUtil.equalObjects(left, as.getLeft()) &&
           InterpreterUtil.equalObjects(right, as.getRight()) &&
           condType == as.getCondType();
  }

  @Override
  public void getBytecodeRange(BitSet values) {
    measureBytecode(values, left);
    measureBytecode(values, right);
    measureBytecode(values);
  }

  @Override
  public void processSforms(SFormsConstructor sFormsConstructor, VarMapHolder varMaps, Statement stat, boolean calcLiveVars) {
    Exprent dest = this.left;
    switch (dest.type) {
      case VAR: {
        final VarExprent destVar = (VarExprent) dest;

        if (this.condType != null) {
          destVar.processSforms(sFormsConstructor, varMaps, stat, calcLiveVars);
          this.getRight().processSforms(sFormsConstructor, varMaps, stat, calcLiveVars);

          // make sure we are in normal form (eg `x &= ...`)
          SFormsFastMapDirect varMap = varMaps.toNormal();

          varMap.setCurrentVar(sFormsConstructor.getOrCreatePhantom(destVar.getVarVersionPair()));
        } else {
          this.getRight().processSforms(sFormsConstructor, varMaps, stat, calcLiveVars);
          sFormsConstructor.updateVarExprent(destVar, stat, varMaps.toNormal(), calcLiveVars);

          if (sFormsConstructor.trackDirectAssignments) {
            switch (this.right.type) {
              case VAR: {
                VarVersionPair rightpaar = ((VarExprent) this.right).getVarVersionPair();
                sFormsConstructor.markDirectAssignment(destVar.getVarVersionPair(), rightpaar);
                break;
              }
              case FIELD: {
                int index = sFormsConstructor.getFieldIndex((FieldExprent) this.right);
                VarVersionPair rightpaar = new VarVersionPair(index, 0);
                sFormsConstructor.markDirectAssignment(destVar.getVarVersionPair(), rightpaar);
                break;
              }
            }
          }
        }

        return;
      }
      case FIELD: {
        this.getLeft().processSforms(sFormsConstructor, varMaps, stat, calcLiveVars);
        varMaps.assertIsNormal(); // the left side of an assignment can't be a boolean expression
        this.getRight().processSforms(sFormsConstructor, varMaps, stat, calcLiveVars);
        varMaps.toNormal();
        varMaps.getNormal().removeAllFields();
        // assignment to a field resets all fields. (could be more precise, but this is easier)
        return;
      }
      default: {
        this.getLeft().processSforms(sFormsConstructor, varMaps, stat, calcLiveVars);
        varMaps.assertIsNormal(); // the left side of an assignment can't be a boolean expression
        this.getRight().processSforms(sFormsConstructor, varMaps, stat, calcLiveVars);
        varMaps.toNormal();
        return;
      }
    }
  }

  // *****************************************************************************
  // getter and setter methods
  // *****************************************************************************

  public Exprent getLeft() {
    return left;
  }

  public Exprent getRight() {
    return right;
  }

  public void setRight(Exprent right) {
    this.right = right;
  }

  /**
   * the type of assignment, eg {@code =}, {@code +=}, {@code -=}, etc.
   */
  public FunctionExprent.FunctionType getCondType() {
    return condType;
  }

  public void setCondType(FunctionExprent.FunctionType condType) {
    this.condType = condType;
  }
}
