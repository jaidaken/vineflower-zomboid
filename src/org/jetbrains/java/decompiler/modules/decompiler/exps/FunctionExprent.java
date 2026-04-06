/*
 * Copyright 2000-2017 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
 */
package org.jetbrains.java.decompiler.modules.decompiler.exps;

import org.jetbrains.java.decompiler.main.ClassesProcessor.ClassNode;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.plugins.PluginImplementationException;
import org.jetbrains.java.decompiler.main.rels.MethodWrapper;
import org.jetbrains.java.decompiler.modules.decompiler.ExprProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.sforms.SFormsConstructor;
import org.jetbrains.java.decompiler.modules.decompiler.sforms.VarMapHolder;
import org.jetbrains.java.decompiler.modules.decompiler.stats.Statement;
import org.jetbrains.java.decompiler.modules.decompiler.vars.CheckTypesResult;
import org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair;
import org.jetbrains.java.decompiler.struct.gen.CodeType;
import org.jetbrains.java.decompiler.struct.gen.TypeFamily;
import org.jetbrains.java.decompiler.struct.gen.VarType;
import org.jetbrains.java.decompiler.struct.gen.generics.GenericType;
import org.jetbrains.java.decompiler.struct.match.MatchEngine;
import org.jetbrains.java.decompiler.struct.match.MatchNode;
import org.jetbrains.java.decompiler.util.IntHelper;
import org.jetbrains.java.decompiler.util.InterpreterUtil;
import org.jetbrains.java.decompiler.util.TextBuffer;
import org.jetbrains.java.decompiler.util.Typed;
import org.jetbrains.java.decompiler.util.collections.ListStack;
import org.jetbrains.java.decompiler.util.collections.SFormsFastMapDirect;

import java.util.*;

public class FunctionExprent extends Exprent {

  private static final CodeType[] TYPE_PRIMITIVES = {CodeType.DOUBLE, CodeType.FLOAT, CodeType.LONG};
  private static final VarType[] TYPES = {VarType.VARTYPE_DOUBLE, VarType.VARTYPE_FLOAT, VarType.VARTYPE_LONG};;

  public enum FunctionType implements Typed {
    ADD(2, "+", 3, null),
    SUB(2, "-", 3, null),
    MUL(2, "*", 2, null),
    DIV(2, "/", 2, null),
    AND(2, "&", 7, null),
    OR(2, "|", 9, null),
    XOR(2, "^", 8, null),
    REM(2, "%", 2, null),
    SHL(2, "<<", 4, null),
    SHR(2, ">>", 4, null),
    USHR(2, ">>>", 4, null),

    BIT_NOT(1, "~", 1, null),
    BOOL_NOT(1, "!", 1, VarType.VARTYPE_BOOLEAN),
    NEG(1, "-", 1, null),

    I2L(VarType.VARTYPE_LONG),
    I2F(VarType.VARTYPE_FLOAT),
    I2D(VarType.VARTYPE_DOUBLE),
    L2I(VarType.VARTYPE_INT),
    L2F(VarType.VARTYPE_FLOAT),
    L2D(VarType.VARTYPE_DOUBLE),
    F2I(VarType.VARTYPE_INT),
    F2L(VarType.VARTYPE_LONG),
    F2D(VarType.VARTYPE_DOUBLE),
    D2I(VarType.VARTYPE_INT),
    D2L(VarType.VARTYPE_LONG),
    D2F(VarType.VARTYPE_FLOAT),
    I2B(VarType.VARTYPE_BYTE),
    I2C(VarType.VARTYPE_CHAR),
    I2S(VarType.VARTYPE_SHORT),

    CAST(2, null, 1, null),
    INSTANCEOF(2, "instanceof", 6, VarType.VARTYPE_BOOLEAN),

    ARRAY_LENGTH(1, null, 0, VarType.VARTYPE_INT),
    IMM(1, "--", 1, null),
    MMI(1, "--", 1, null),
    IPP(1, "++", 1, null),
    PPI(1, "++", 1, null),

    TERNARY(3, null, 12, null),

    LCMP(2, "__lcmp__", -1, VarType.VARTYPE_BOOLEAN),
    FCMPL(2, "__fcmpl__", -1, VarType.VARTYPE_BOOLEAN),
    FCMPG(2, "__fcmpg__", -1, VarType.VARTYPE_BOOLEAN),
    DCMPL(2, "__dcmpl__", -1, VarType.VARTYPE_BOOLEAN),
    DCMPG(2, "__dcmpg__", -1, VarType.VARTYPE_BOOLEAN),

    EQ(2, "==", 6, VarType.VARTYPE_BOOLEAN),
    NE(2, "!=", 6, VarType.VARTYPE_BOOLEAN),
    LT(2, "<", 5, VarType.VARTYPE_BOOLEAN),
    GE(2, ">=", 5, VarType.VARTYPE_BOOLEAN),
    GT(2, ">", 5, VarType.VARTYPE_BOOLEAN),
    LE(2, "<=", 5, VarType.VARTYPE_BOOLEAN),

    BOOLEAN_AND(2, "&&", 10, VarType.VARTYPE_BOOLEAN),
    BOOLEAN_OR(2, "||", 11, VarType.VARTYPE_BOOLEAN),
    STR_CONCAT(2, "+", 3, VarType.VARTYPE_STRING),

    // Catch all for plugins

    OTHER(0, "??????", 999, null)
    ;

    public final int arity;
    public final String operator;
    public final int precedence;
    public final VarType castType;
    final VarType type;

    FunctionType(int arity, String operator, int precedence, VarType type) {
      this(arity, operator, precedence, null, type);
    }

    FunctionType(VarType castType) {
      this(1, null, 1, castType, castType);
    }

    FunctionType(int arity, String operator, int precedence, VarType castType, VarType type) {
      this.arity = arity;
      this.operator = operator;
      this.precedence = precedence;
      this.castType = castType;
      this.type = type;
    }

    public boolean isArithmeticBinaryOperation() {
      return ordinal() <= USHR.ordinal();
    }

    public boolean isMM() {
      return this == MMI || this == IMM;
    }

    public boolean isPP() {
      return this == PPI || this == IPP;
    }

    public boolean isPPMM() {
      return isPP() || isMM();
    }

    public boolean isPostfixPPMM() {
      return this == IMM || this == IPP;
    }

    public boolean isComparison() {
      return this == EQ || this == NE || this == LT || this == GE || this == GT || this == LE;
    }
  }

  private static final Set<FunctionType> ASSOCIATIVITY = new HashSet<>(Arrays.asList(
    FunctionType.ADD, FunctionType.MUL, FunctionType.AND, FunctionType.OR, FunctionType.XOR, FunctionType.BOOLEAN_AND, FunctionType.BOOLEAN_OR, FunctionType.STR_CONCAT));

  private FunctionType funcType;
  private VarType implicitType;
  private final List<Exprent> lstOperands;
  private boolean needsCast = true;
  // When true, prevent NE/EQ simplification that collapses bool != 0 to bare bool.
  // Used by IfExprent for variables declared with 'var' and int-constant init.
  private boolean forceLiteral = false;
  private boolean disableNewlineGroupCreation = false;

  public FunctionExprent(FunctionType funcType, ListStack<Exprent> stack, BitSet bytecodeOffsets) {
    this(funcType, new ArrayList<>(), bytecodeOffsets);

    if (funcType.arity == 1) {
      lstOperands.add(stack.pop());
    }
    else if (funcType.arity == 2) {
      Exprent expr = stack.pop();
      lstOperands.add(stack.pop());
      lstOperands.add(expr);
    }
    else {
      throw new RuntimeException("no direct instantiation possible: " + funcType);
    }
  }

  public FunctionExprent(FunctionType funcType, List<Exprent> operands, BitSet bytecodeOffsets) {
    super(Type.FUNCTION);
    this.funcType = funcType;
    this.lstOperands = operands;

    addBytecodeOffsets(bytecodeOffsets);
  }

  public FunctionExprent(FunctionType funcType, Exprent operand, BitSet bytecodeOffsets) {
    this(funcType, new ArrayList<>(1), bytecodeOffsets);
    lstOperands.add(operand);
  }

  @Override
  public VarType getExprType() {
    VarType staticType = funcType.type;
    if (staticType != null) {
      return staticType;
    }

    switch (funcType) {
      case IMM:
      case MMI:
      case IPP:
      case PPI:
        return implicitType;
      case SHL:
      case SHR:
      case USHR:
      case BIT_NOT:
      case NEG:
        return getMaxVarType(lstOperands.get(0).getExprType());
      case ADD: {
        VarType left = lstOperands.get(0).getExprType();
        VarType right = lstOperands.get(1).getExprType();
        // String + anything = String (Java string concatenation)
        if (VarType.VARTYPE_STRING.equals(left) || VarType.VARTYPE_STRING.equals(right)) {
          return VarType.VARTYPE_STRING;
        }
        return getMaxVarType(left, right);
      }
      case SUB:
      case MUL:
      case DIV:
      case REM:
        return getMaxVarType(lstOperands.get(0).getExprType(), lstOperands.get(1).getExprType());
      case AND:
      case OR:
      case XOR: {
        VarType type1 = lstOperands.get(0).getExprType();
        VarType type2 = lstOperands.get(1).getExprType();
        if (type1.type == CodeType.BOOLEAN && type2.type == CodeType.BOOLEAN) {
          return VarType.VARTYPE_BOOLEAN;
        } else {
          return getMaxVarType(type1, type2);
        }
      }
      case CAST:
        return lstOperands.get(1).getExprType();
      case TERNARY: {
        Exprent param1 = lstOperands.get(1);
        Exprent param2 = lstOperands.get(2);
        VarType supertype = VarType.getCommonSupertype(param1.getExprType(), param2.getExprType());
        if (supertype == null) {
          throw new IllegalStateException("No common supertype for ternary expression");
        }

        if (param1 instanceof ConstExprent && param2 instanceof ConstExprent &&
          supertype.type != CodeType.BOOLEAN && VarType.VARTYPE_INT.isSuperset(supertype)) {
          return VarType.VARTYPE_INT;
        } else {
          return supertype;
        }
      }
      case OTHER: throw new PluginImplementationException();
      default: throw new IllegalStateException("No type for funcType=" + funcType);
    }
  }

  @Override
  public VarType getInferredExprType(VarType upperBound) {
    if (funcType == FunctionType.CAST) {
      this.needsCast = true;
      VarType right = lstOperands.get(0).getInferredExprType(upperBound);
      List<VarType> cast = lstOperands.subList(1, lstOperands.size()).stream().map(Exprent::getExprType).toList();

      if (upperBound != null && (upperBound.isGeneric() || right.isGeneric())) {
        Map<VarType, List<VarType>> names = this.getNamedGenerics();
        int arrayDim = 0;

        if (upperBound.arrayDim == right.arrayDim && upperBound.arrayDim > 0) {
          arrayDim = upperBound.arrayDim;
          upperBound = upperBound.resizeArrayDim(0);
          right = right.resizeArrayDim(0);
        }

        List<VarType> types = names.get(right);
        if (types == null) {
          types = names.get(upperBound);
        }

        if (types != null) {
          List<VarType> finalTypes = types;
          if (cast.stream().allMatch(castType -> finalTypes.stream().anyMatch(type -> DecompilerContext.getStructContext().instanceOf(type.value, castType.value)))) {
            this.needsCast = false;
          }
        } else {
            this.needsCast = right.type == CodeType.NULL || !DecompilerContext.getStructContext().instanceOf(right.value, upperBound.value) || !areGenericTypesSame(right, upperBound);
        }

        if (!this.needsCast) {
          if (arrayDim > 0) {
            right = right.resizeArrayDim(arrayDim);
          }

          return right;
        }
      } else { //TODO: Capture generics to make cast better?
        final VarType finalRight = right;
        this.needsCast = right.type == CodeType.NULL || cast.stream().anyMatch(castType -> !DecompilerContext.getStructContext().instanceOf(finalRight.value, castType.value)) || cast.stream().anyMatch(castType -> finalRight.arrayDim != castType.arrayDim);
      }

      return getExprType();
    } else if (funcType == FunctionType.TERNARY) {
      VarType type1 = lstOperands.get(1).getInferredExprType(upperBound);
      VarType type2 = lstOperands.get(2).getInferredExprType(upperBound);

      if (type1.type == CodeType.NULL) {
        return type2;
      } else if (type2.type == CodeType.NULL) {
        return type1;
      }

      VarType union = VarType.getCommonSupertype(type1, type2);

      if (union != null && lstOperands.get(1) instanceof ConstExprent && lstOperands.get(2) instanceof ConstExprent &&
        union.type != CodeType.BOOLEAN && VarType.VARTYPE_INT.isSuperset(union)) {
        union = VarType.VARTYPE_INT;
      }

      return union != null ? union : getExprType();
    } else if (funcType == FunctionType.INSTANCEOF) {
      for (Exprent oper : lstOperands) {
        oper.getInferredExprType(null);
      }
      return getExprType();
    }

    // All operands should be informed about the upper bound here
    for (Exprent oper : lstOperands) {
      oper.getInferredExprType(upperBound);
    }

    return getExprType();
  }

  private static boolean areGenericTypesSame(VarType right, VarType upperBound) {
    if (!(right instanceof GenericType && upperBound instanceof GenericType)) {
      return true; // Prevent this from accidentally always casting
    }

    GenericType rightGeneric = (GenericType)right;
    GenericType upperBoundGeneric = (GenericType)upperBound;

    // Different argument counts, can't be the same!
    if (rightGeneric.getArguments().size() != upperBoundGeneric.getArguments().size()) {
      return false;
    }

    for (int i = 0; i < upperBoundGeneric.getArguments().size(); i++) {
      VarType upperType = upperBoundGeneric.getArguments().get(i);
      VarType rightType = rightGeneric.getArguments().get(i);

      // Trying to cast Obj<?> to Obj<T>, which is an unchecked cast- needs to be explicit
      if (upperType != null && rightType == null) {
        return false;
      }
    }

    return true;
  }

  @Override
  public int getExprentUse() {
    if (funcType.ordinal() >= FunctionType.IMM.ordinal() && funcType.ordinal() <= FunctionType.PPI.ordinal()) {
      return 0;
    }
    else {
      int ret = Exprent.MULTIPLE_USES | Exprent.SIDE_EFFECTS_FREE;
      for (Exprent expr : lstOperands) {
        ret &= expr.getExprentUse();
      }
      return ret;
    }
  }

  @Override
  public CheckTypesResult checkExprTypeBounds() {
    CheckTypesResult result = new CheckTypesResult();

    Exprent param1 = lstOperands.get(0);
    VarType type1 = param1.getExprType();
    Exprent param2 = null;
    VarType type2 = null;

    if (lstOperands.size() > 1) {
      param2 = lstOperands.get(1);
      type2 = param2.getExprType();
    }

    switch (funcType) {
      case TERNARY:
        VarType supertype = getExprType();
        result.addMinTypeExprent(param1, VarType.VARTYPE_BOOLEAN);
        result.addMinTypeExprent(param2, VarType.getMinTypeInFamily(supertype.typeFamily));
        result.addMinTypeExprent(lstOperands.get(2), VarType.getMinTypeInFamily(supertype.typeFamily));
        break;
      case I2L:
      case I2F:
      case I2D:
      case I2B:
      case I2C:
      case I2S:
        result.addMinTypeExprent(param1, VarType.VARTYPE_BYTECHAR);
        result.addMaxTypeExprent(param1, VarType.VARTYPE_INT);
        break;
      case IMM:
      case IPP:
      case MMI:
      case PPI:
        result.addMinTypeExprent(param1, implicitType);
        result.addMaxTypeExprent(param1, implicitType);
        break;
      case ADD:
      case SUB:
      case MUL:
      case DIV:
      case REM:
      case SHL:
      case SHR:
      case USHR:
      case LT:
      case GE:
      case GT:
      case LE:
        result.addMinTypeExprent(param2, VarType.VARTYPE_BYTECHAR);
      case BIT_NOT:
        // case BOOL_NOT:
      case NEG:
        result.addMinTypeExprent(param1, VarType.VARTYPE_BYTECHAR);
        break;
      case AND:
      case OR:
      case XOR:
      case EQ:
      case NE: {
        if (type1.type == CodeType.BOOLEAN) {
          if (type2.isStrictSuperset(type1)) {
            result.addMinTypeExprent(param1, VarType.VARTYPE_BYTECHAR);
          }
          else { // both are booleans
            boolean param1_false_boolean = (param1 instanceof ConstExprent && !((ConstExprent)param1).hasBooleanValue());
            boolean param2_false_boolean = (param2 instanceof ConstExprent && !((ConstExprent)param2).hasBooleanValue());

            if (param1_false_boolean || param2_false_boolean) {
              result.addMinTypeExprent(param1, VarType.VARTYPE_BYTECHAR);
              result.addMinTypeExprent(param2, VarType.VARTYPE_BYTECHAR);
            }
          }
        }
        else if (type2.type == CodeType.BOOLEAN) {
          if (type1.isStrictSuperset(type2)) {
            result.addMinTypeExprent(param2, VarType.VARTYPE_BYTECHAR);
          }
        }
        break;
      }
      case INSTANCEOF:
        if (lstOperands.size() > 2 && lstOperands.get(2) instanceof VarExprent var) { // pattern matching instanceof
          // The type of the defined var must be the type being tested
          result.addMinTypeExprent(var, lstOperands.get(1).getExprType());
        }
        break;
      case STR_CONCAT:
        VarType type = this.implicitType == null ? VarType.VARTYPE_STRING : this.implicitType;
        // Inform children of the type of string concat that we are
        if (type1.typeFamily == type.typeFamily) {
          result.addMinTypeExprent(param1, type);
        }

        if (type2.typeFamily == type.typeFamily) {
          result.addMinTypeExprent(param2, type);
        }
        break;

      case OTHER: throw new PluginImplementationException();
    }

    return result;
  }

  @Override
  public List<Exprent> getAllExprents(List<Exprent> lst) {
    lst.addAll(this.lstOperands);
    return lst;
  }

  @Override
  public Exprent copy() {
    List<Exprent> lst = new ArrayList<>();
    for (Exprent expr : lstOperands) {
      lst.add(expr.copy());
    }
    FunctionExprent func = new FunctionExprent(funcType, lst, bytecode);
    func.setImplicitType(implicitType);

    return func;
  }

  /**
   * RTF: when an operand in an arithmetic expression is an InvocationExprent
   * whose descriptor returns Object but the operand's VF type is a primitive,
   * wrap the rendered operand with a cast to the primitive type.
   */
  private static TextBuffer rtfCastObjectOperand(Exprent operand, TextBuffer rendered, VarType otherType) {
    // Unwrap casts and unboxing calls to find the underlying invocation
    Exprent inner = operand;
    while (inner instanceof FunctionExprent
        && ((FunctionExprent) inner).getFuncType() == FunctionType.CAST) {
      inner = ((FunctionExprent) inner).getLstOperands().get(0);
    }
    // Unwrap unboxing calls (e.g., intValue(), booleanValue()) to find
    // the underlying method call whose descriptor returns Object
    if (inner instanceof InvocationExprent && ((InvocationExprent) inner).isUnboxingCall()) {
      Exprent inst = ((InvocationExprent) inner).getInstance();
      if (inst != null) {
        // Unwrap casts on the instance too
        while (inst instanceof FunctionExprent
            && ((FunctionExprent) inst).getFuncType() == FunctionType.CAST) {
          inst = ((FunctionExprent) inst).getLstOperands().get(0);
        }
        if (inst instanceof InvocationExprent) {
          inner = inst;
        }
      }
    }
    if (inner instanceof InvocationExprent) {
      String desc = ((InvocationExprent) inner).getStringDescriptor();
      if (desc != null && desc.endsWith(")Ljava/lang/Object;")) {
        VarType exprType = operand.getExprType();
        // Cast primitives (int, long, etc.)
        if (exprType.type != CodeType.OBJECT && exprType.type != CodeType.NULL
            && exprType.type != CodeType.UNKNOWN) {
          return rendered.enclose("(" + ExprProcessor.getCastTypeName(exprType) + ")", "");
        }
        // When the type is still Object (not narrowed), the operand can't be
        // used in arithmetic. Cast to the type that the OTHER operand implies.
        // E.g., Object + 1000L → cast to (long); 1 + Object → cast to (int).
        if (exprType.type == CodeType.OBJECT && "java/lang/Object".equals(exprType.value)) {
          VarType inferredType = operand.getInferredExprType(null);
          if (inferredType != null && inferredType.type != CodeType.NULL
              && inferredType.type != CodeType.UNKNOWN
              && !"java/lang/Object".equals(inferredType.value)) {
            // For boxed types (Integer, Long), cast to the boxed type
            return rendered.enclose("(" + ExprProcessor.getCastTypeName(inferredType) + ")", "");
          }
          // Fallback: use the other operand's type to determine the cast.
          // For int + Object, cast Object to (int); for Object + long, cast to (long).
          if (otherType != null && otherType.type != CodeType.OBJECT
              && otherType.type != CodeType.NULL && otherType.type != CodeType.UNKNOWN) {
            return rendered.enclose("(" + ExprProcessor.getCastTypeName(otherType) + ")", "");
          }
        }
      }
    }
    return rendered;
  }

  /**
   * Checks if an operand is boolean-typed for the purpose of simplifying NE/EQ with 0/1.
   * Covers: explicit boolean type, LVT boolean descriptor, var-declared variables
   * (which may render as boolean), and boolean-producing AND expressions.
   */
  private static boolean isBoolishOperand(Exprent expr) {
    VarType type = expr.getExprType();
    if (type.equals(VarType.VARTYPE_BOOLEAN)) return true;
    // BYTECHAR is the common internal type for booleans at the bytecode level
    if (type.type == CodeType.BOOLEAN) return true;
    if (expr instanceof VarExprent) {
      VarExprent ve = (VarExprent) expr;
      // Check LVT descriptor for boolean type
      if (ve.getLVT() != null && "Z".equals(ve.getLVT().getDescriptor())) return true;
      // Check VarProcessor type
      if (ve.getProcessor() != null) {
        VarType procType = ve.getProcessor().getVarType(ve.getVarVersionPair());
        if (procType != null && (procType.equals(VarType.VARTYPE_BOOLEAN) || procType.type == CodeType.BOOLEAN)) return true;
      }
    }
    if (expr instanceof FunctionExprent) {
      FunctionExprent fe = (FunctionExprent) expr;
      // AND/OR with a constant-0 operand or boolean operand produces boolean
      if (fe.funcType == FunctionType.AND || fe.funcType == FunctionType.OR) {
        for (Exprent op : fe.getLstOperands()) {
          if (isBoolishOperand(op)) return true;
        }
      }
      // Comparison operators produce boolean
      if (fe.funcType.isComparison()) return true;
      // BOOLEAN_AND/OR produce boolean
      if (fe.funcType == FunctionType.BOOLEAN_AND || fe.funcType == FunctionType.BOOLEAN_OR) return true;
    }
    return false;
  }

  @Override
  public boolean equals(Object o) {
    if (o == this) return true;
    if (!(o instanceof FunctionExprent)) return false;

    FunctionExprent fe = (FunctionExprent)o;
    return funcType == fe.getFuncType() &&
           InterpreterUtil.equalLists(lstOperands, fe.getLstOperands()); // TODO: order of operands insignificant
  }

  @Override
  public void replaceExprent(Exprent oldExpr, Exprent newExpr) {
    for (int i = 0; i < lstOperands.size(); i++) {
      if (oldExpr == lstOperands.get(i)) {
        lstOperands.set(i, newExpr);
      }
    }
  }

  @Override
  public TextBuffer toJava(int indent) {
    if (funcType == FunctionType.OTHER) {
      throw new PluginImplementationException();
    }

    TextBuffer buf = new TextBuffer();
    buf.addBytecodeMapping(bytecode);

    // If we're an unsigned right shift or lower, this function can be represented as a single leftHand + functionType + rightHand operation.
    if (this.funcType.isArithmeticBinaryOperation()) {
      Exprent left = this.lstOperands.get(0);
      Exprent right = this.lstOperands.get(1);

      // Minecraft specific hot fix: If we're doing arithmetic or bitwise math by a char value, we can assume that it's wrong behavior.
      // We check for this and then fix it by resetting the param to be an int instead of a char.
      // This fixes cases where "& 65535" and "& 0xFFFF" get wrongly decompiled as "& '\uffff'".
      if (this.funcType.isArithmeticBinaryOperation()) {
        // Checks to see if the right expression is a constant and then adjust the type from char to int if the left is an int.
        // Failing that, check the left hand side and then do the same.
        if (right instanceof ConstExprent) {
          ((ConstExprent) right).adjustConstType(left.getExprType());
          // Boolean constants in arithmetic context are always wrong (Java forbids boolean in math)
          ((ConstExprent) right).forceBooleanToInt();
        } else if (left instanceof ConstExprent) {
          ((ConstExprent) left).adjustConstType(right.getExprType());
          ((ConstExprent) left).forceBooleanToInt();
        }
      }

      // Initialize the operands with the defaults
      TextBuffer leftOperand = wrapOperandString(left, false, indent, true);
      TextBuffer rightOperand = wrapOperandString(right, true, indent, true);

      // RTF: when an operand is an InvocationExprent returning Object (from
      // descriptor) but VF narrowed it to a primitive, the rendered Java has
      // Object in an arithmetic context. Insert a cast to the primitive type.
      if (DecompilerContext.isRoundtripFidelity()) {
        leftOperand = rtfCastObjectOperand(left, leftOperand, right.getExprType());
        rightOperand = rtfCastObjectOperand(right, rightOperand, left.getExprType());
      }

      // Check for special cased integers on the right and left hand side, and then return if they are found.
      // This only applies to bitwise and as well as bitwise or functions.
      if (this.funcType == FunctionType.AND || this.funcType == FunctionType.OR) {
        // RTF: when bitwise AND has a constant 0 operand and the other is a boolean
        // comparison, the bytecode pattern is `iconst_0; comparison; iand`. In Java,
        // `0 & (a != b)` has type issues (int & boolean). Render as `false & (expr)`
        // instead, which is valid boolean & boolean and produces identical bytecode.
        boolean convertedToBoolAnd = false;
        if (DecompilerContext.isRoundtripFidelity() && this.funcType == FunctionType.AND) {
          boolean leftIsZero = left instanceof ConstExprent
              && Integer.valueOf(0).equals(((ConstExprent) left).getValue());
          boolean rightIsZero = right instanceof ConstExprent
              && Integer.valueOf(0).equals(((ConstExprent) right).getValue());
          boolean rightIsBool = right.getExprType().equals(VarType.VARTYPE_BOOLEAN)
              || (right instanceof FunctionExprent && ((FunctionExprent) right).funcType.isComparison());
          boolean leftIsBool = left.getExprType().equals(VarType.VARTYPE_BOOLEAN)
              || (left instanceof FunctionExprent && ((FunctionExprent) left).funcType.isComparison());

          if (leftIsZero && rightIsBool) {
            leftOperand.setLength(0);
            leftOperand.append("false");
            rightOperand = new TextBuffer().append("(").append(wrapOperandString(right, true, indent, true)).append(")");
            convertedToBoolAnd = true;
          } else if (rightIsZero && leftIsBool) {
            rightOperand.setLength(0);
            rightOperand.append("false");
            leftOperand = new TextBuffer().append("(").append(wrapOperandString(left, false, indent, true)).append(")");
            convertedToBoolAnd = true;
          }
        }

        if (!convertedToBoolAnd) {
          // Check if the right is an int constant and adjust accordingly
          if (right instanceof ConstExprent && right.getExprType() == VarType.VARTYPE_INT) {
            Integer value = (Integer) ((ConstExprent)right).getValue();
            rightOperand.setLength(0);
            rightOperand.append(IntHelper.adjustedIntRepresentation(value));
          }

          // Check if the left is an int constant and adjust accordingly
          if (left instanceof ConstExprent && left.getExprType() == VarType.VARTYPE_INT) {
            Integer value = (Integer) ((ConstExprent)left).getValue();
            leftOperand.setLength(0);
            leftOperand.append(IntHelper.adjustedIntRepresentation(value));
          }
        }
      }

      // Return the applied operands and operators.
      if (!disableNewlineGroupCreation) {
        buf.pushNewlineGroup(indent, 1);
      }
      buf.append(leftOperand)
        .appendPossibleNewline(" ").append(funcType.operator).append(" ")
        .append(rightOperand);
      if (!disableNewlineGroupCreation) {
        buf.popNewlineGroup();
      }

      return buf;
    }

      // try to determine more accurate type for 'char' literals
    if (funcType.ordinal() >= FunctionType.EQ.ordinal()) {
      Exprent left = lstOperands.get(0);
      Exprent right = lstOperands.get(1);

      // RTF: simplify boolean-vs-int comparisons for NE/EQ.
      // When one operand is boolean (from LVT or expression type) and the other
      // is constant 0/1, Java doesn't allow `bool != 0`. Simplify to `bool`/`!bool`.
      // Skip when forceLiteral is set (synthetic NE from IfExprent for var-int-init vars).
      if (DecompilerContext.isRoundtripFidelity() && !forceLiteral
          && (funcType == FunctionType.NE || funcType == FunctionType.EQ)) {
        Exprent boolOp = null;
        ConstExprent constOp = null;
        if (right instanceof ConstExprent && isBoolishOperand(left)) {
          boolOp = left; constOp = (ConstExprent) right;
        } else if (left instanceof ConstExprent && isBoolishOperand(right)) {
          boolOp = right; constOp = (ConstExprent) left;
        }
        if (boolOp != null && constOp.getValue() instanceof Integer) {
          int val = (Integer) constOp.getValue();
          if (val == 0 || val == 1) {
            boolean negate = (funcType == FunctionType.EQ && val == 0)
                || (funcType == FunctionType.NE && val == 1);
            TextBuffer boolBuf = boolOp.toJava(indent);
            if (negate) {
              buf.append("!").append(boolBuf);
            } else {
              buf.append(boolBuf);
            }
            return buf;
          }
        }
      }

      if (funcType.ordinal() <= FunctionType.LE.ordinal()) {
        if (right instanceof ConstExprent) {
          var other = left.getExprType();
          if (other != null) {
            ((ConstExprent) right).adjustConstType(other);
            // Boolean constant compared against non-boolean: force to int
            if (other.typeFamily != TypeFamily.BOOLEAN) {
              ((ConstExprent) right).forceBooleanToInt();
            }
          }
        }
        else if (left instanceof ConstExprent) {
          var other = right.getExprType();
          if (other != null) {
            ((ConstExprent) left).adjustConstType(other);
            if (other.typeFamily != TypeFamily.BOOLEAN) {
              ((ConstExprent) left).forceBooleanToInt();
            }
          }
        }
      }

      TextBuffer leftOp = wrapOperandString(left, false, indent, true);
      TextBuffer rightOp = wrapOperandString(right, true, indent, true);
      if (DecompilerContext.isRoundtripFidelity()) {
        leftOp = rtfCastObjectOperand(left, leftOp, right.getExprType());
        rightOp = rtfCastObjectOperand(right, rightOp, left.getExprType());
        // RTF: && and || require boolean operands, but merged int/boolean vars may
        // have int DECLARATION type even though VarExprent.getExprType() returns boolean.
        // Check both the expression type and the VarExprent's varType (declaration type).
        if (funcType == FunctionType.BOOLEAN_AND || funcType == FunctionType.BOOLEAN_OR) {
          if (needsBoolConversion(left)) {
            leftOp = new TextBuffer().append("(").append(leftOp).append(" != 0)");
          }
          if (needsBoolConversion(right)) {
            rightOp = new TextBuffer().append("(").append(rightOp).append(" != 0)");
          }
        }
      }
      if (!disableNewlineGroupCreation) {
        buf.pushNewlineGroup(indent, 1);
      }
      buf.append(leftOp)
        .appendPossibleNewline(" ").append(funcType.operator).append(" ")
        .append(rightOp);
      if (!disableNewlineGroupCreation) {
        buf.popNewlineGroup();
      }
      return buf;
    }

    switch (funcType) {
      case BIT_NOT:
      case BOOL_NOT:
      case NEG:
      case MMI:
      case PPI:
        return buf.append(wrapOperandString(lstOperands.get(0), true, indent).prepend(funcType.operator));
      case IPP:
      case IMM:
        return buf.append(wrapOperandString(lstOperands.get(0), true, indent).append(funcType.operator));
      case CAST:
        if (!needsCast) {
          // RTF: force rendering when source is Object and target is generic.
          // Without the cast, javac may infer a more specific incompatible generic
          // type (e.g., HashSet<Object> from raw method references in collect),
          // causing generic invariance errors. The intermediate raw cast in the
          // full rendering path produces (Set<Integer>)(Set)expr which is safe.
          boolean forceGenericCast = false;
          if (DecompilerContext.isRoundtripFidelity() && lstOperands.size() >= 2) {
            VarType srcType = lstOperands.get(0).getExprType();
            VarType tgtType = lstOperands.get(1).getExprType();
            if (srcType.type == CodeType.OBJECT && "java/lang/Object".equals(srcType.value)
                && tgtType instanceof GenericType
                && !((GenericType) tgtType).getArguments().isEmpty()) {
              forceGenericCast = true;
            }
          }
          if (!forceGenericCast) {
            return buf.append(lstOperands.get(0).toJava(indent));
          }
        }
        for (int i = 1; i < lstOperands.size(); i++) {
          if (i > 1) {
            buf.append(" & ");
          }
          buf.append(lstOperands.get(i).toJava(indent));
        }
        {
          TextBuffer castExprBuf = wrapOperandString(lstOperands.get(0), true, indent);
          // RTF: when the source type is provably incompatible with the cast target,
          // add an intermediate (Object) cast. This happens when type inference narrows
          // a variable slot to one specific type but the slot holds other types too.
          if (DecompilerContext.isRoundtripFidelity() && lstOperands.size() >= 2) {
            VarType sourceType = lstOperands.get(0).getExprType();
            VarType targetType = lstOperands.get(1).getExprType();
            if (sourceType.type == CodeType.OBJECT && targetType.type == CodeType.OBJECT
                && sourceType.value != null && targetType.value != null
                && !"java/lang/Object".equals(sourceType.value)
                && !"java/lang/Object".equals(targetType.value)) {
              boolean compatible = DecompilerContext.getStructContext() != null
                  && (DecompilerContext.getStructContext().instanceOf(sourceType.value, targetType.value)
                      || DecompilerContext.getStructContext().instanceOf(targetType.value, sourceType.value));
              if (!compatible) {
                castExprBuf = castExprBuf.enclose("(Object)", "");
              }
            }
            // RTF: generic invariance - insert intermediate raw-type cast when:
            // 1. Source and target have the same base class (or subtype) but different
            //    type arguments (e.g., List<Biome> to List<IBiome>).
            // 2. Source is Object but target is generic - javac may infer a more specific
            //    source type from context (e.g., HashSet<Object> from raw collect),
            //    causing invariance errors.
            VarType srcInferred = lstOperands.get(0).getInferredExprType(null);
            boolean needsRawIntermediate = false;
            if (srcInferred instanceof GenericType && targetType instanceof GenericType
                && srcInferred.value != null && targetType.value != null) {
              boolean sameOrSubtype = srcInferred.value.equals(targetType.value)
                  || (DecompilerContext.getStructContext() != null
                      && DecompilerContext.getStructContext().instanceOf(srcInferred.value, targetType.value));
              if (sameOrSubtype) {
                GenericType srcGen = (GenericType) srcInferred;
                GenericType tgtGen = (GenericType) targetType;
                if (!srcGen.getArguments().isEmpty() && !tgtGen.getArguments().isEmpty()
                    && !srcGen.getArguments().equals(tgtGen.getArguments())) {
                  needsRawIntermediate = true;
                }
              }
            }
            // Object source with generic target: javac may infer a more specific
            // incompatible generic type (e.g., from raw method references in collect)
            if (!needsRawIntermediate
                && "java/lang/Object".equals(sourceType.value)
                && targetType instanceof GenericType
                && !((GenericType)targetType).getArguments().isEmpty()) {
              needsRawIntermediate = true;
            }
            if (needsRawIntermediate) {
              String rawName = ExprProcessor.getCastTypeName(
                  new VarType(CodeType.OBJECT, targetType.arrayDim, targetType.value));
              castExprBuf = castExprBuf.enclose("(" + rawName + ")", "");
            }
          }
          return buf.encloseWithParens().append(castExprBuf);
        }
      case ARRAY_LENGTH:
        Exprent arr = lstOperands.get(0);

        buf.append(wrapOperandString(arr, false, indent));
        if (arr.getExprType().arrayDim == 0) {
          VarType objArr = VarType.VARTYPE_OBJECT.resizeArrayDim(1); // type family does not change
          buf.enclose("((" + ExprProcessor.getCastTypeName(objArr) + ")", ")");
          buf.addTypeNameToken(objArr, 2);
        }
        return buf.append(".length");
      case TERNARY: {
        buf.pushNewlineGroup(indent, 1);
        TextBuffer condBuf = wrapOperandString(lstOperands.get(0), true, indent);
        // RTF: when ternary condition's Java type would be Object (from raw method
        // return), cast to boolean. Object can't be used as boolean in Java.
        // VF's getExprType() may have narrowed the type, so check the method descriptor.
        if (DecompilerContext.isRoundtripFidelity()) {
          Exprent condExpr = lstOperands.get(0);
          boolean needsBoolCast = false;
          if (condExpr instanceof InvocationExprent) {
            String desc = ((InvocationExprent) condExpr).getStringDescriptor();
            needsBoolCast = desc != null && desc.endsWith(")Ljava/lang/Object;");
          }
          if (!needsBoolCast) {
            VarType condType = condExpr.getExprType();
            needsBoolCast = condType.type == CodeType.OBJECT && "java/lang/Object".equals(condType.value);
          }
          if (needsBoolCast) {
            condBuf = condBuf.enclose("(boolean)", "");
          }

          // RTF: when both ternary branches are unboxing calls (e.g. .booleanValue()),
          // force them to be printed explicitly. Without this, auto-unboxing elision
          // causes javac to emit a single shared unboxing call after the branch merge,
          // producing one fewer instruction than the original's per-branch calls.
          Exprent op1 = lstOperands.get(1);
          Exprent op2 = lstOperands.get(2);
          if (op1 instanceof InvocationExprent inv1 && inv1.isUnboxingCall()
              && op2 instanceof InvocationExprent inv2 && inv2.isUnboxingCall()) {
            inv1.forceUnboxing(true);
            inv2.forceUnboxing(true);
          }

          // RTF: detect !a && !b ? X : Y (De Morgan from collapseIfIf) and render
          // as a || b ? Y : X to preserve the original branch polarity. The && form
          // compiles with ifne;ifne (both jump to false), while || compiles with
          // ifne;ifeq (first jumps to true, second jumps to false), matching the
          // original bytecode's shared-target pattern.
          Exprent condExpr2 = lstOperands.get(0);
          if (condExpr2 instanceof FunctionExprent condFunc) {
            FunctionType condFuncType = condFunc.getFuncType();
            // Pattern 1: !a && !b ? X : Y → a || b ? Y : X
            if (condFuncType == FunctionType.BOOLEAN_AND) {
              List<Exprent> andOps = condFunc.getLstOperands();
              if (andOps.size() == 2
                  && andOps.get(0) instanceof FunctionExprent f0 && f0.getFuncType() == FunctionType.BOOL_NOT
                  && andOps.get(1) instanceof FunctionExprent f1 && f1.getFuncType() == FunctionType.BOOL_NOT) {
                List<Exprent> orOps = new ArrayList<>();
                orOps.add(f0.getLstOperands().get(0));
                orOps.add(f1.getLstOperands().get(0));
                FunctionExprent orExpr = new FunctionExprent(FunctionType.BOOLEAN_OR, orOps, condFunc.bytecode);
                condBuf = wrapOperandString(orExpr, true, indent);
                buf.append(condBuf)
                  .appendPossibleNewline(" ").append("? ")
                  .append(wrapOperandString(lstOperands.get(2), true, indent))
                  .appendPossibleNewline(" ").append(": ")
                  .append(wrapOperandString(lstOperands.get(1), true, indent));
                buf.popNewlineGroup();
                return buf;
              }
            }
            // Pattern 2: !a || !b ? X : Y → a && b ? Y : X
            if (condFuncType == FunctionType.BOOLEAN_OR) {
              List<Exprent> orOps = condFunc.getLstOperands();
              if (orOps.size() == 2
                  && orOps.get(0) instanceof FunctionExprent f0 && f0.getFuncType() == FunctionType.BOOL_NOT
                  && orOps.get(1) instanceof FunctionExprent f1 && f1.getFuncType() == FunctionType.BOOL_NOT) {
                List<Exprent> andOps = new ArrayList<>();
                andOps.add(f0.getLstOperands().get(0));
                andOps.add(f1.getLstOperands().get(0));
                FunctionExprent andExpr = new FunctionExprent(FunctionType.BOOLEAN_AND, andOps, condFunc.bytecode);
                condBuf = wrapOperandString(andExpr, true, indent);
                buf.append(condBuf)
                  .appendPossibleNewline(" ").append("? ")
                  .append(wrapOperandString(lstOperands.get(2), true, indent))
                  .appendPossibleNewline(" ").append(": ")
                  .append(wrapOperandString(lstOperands.get(1), true, indent));
                buf.popNewlineGroup();
                return buf;
              }
            }
          }
        }
        // Force boolean→int in ternary branches when the other branch is int.
        // Fixes "cond ? 4 : false" → "cond ? 4 : 0" (Java forbids int/boolean mix in ternary)
        Exprent branch1 = lstOperands.get(1);
        Exprent branch2 = lstOperands.get(2);
        if (branch1 instanceof ConstExprent && branch2 instanceof ConstExprent) {
          TypeFamily f1 = branch1.getExprType().typeFamily;
          TypeFamily f2 = branch2.getExprType().typeFamily;
          if (f1 == TypeFamily.INTEGER && f2 == TypeFamily.BOOLEAN) {
            ((ConstExprent) branch2).forceBooleanToInt();
          } else if (f2 == TypeFamily.INTEGER && f1 == TypeFamily.BOOLEAN) {
            ((ConstExprent) branch1).forceBooleanToInt();
          }
        } else if (branch1 instanceof ConstExprent && branch2.getExprType().typeFamily == TypeFamily.INTEGER
            && branch1.getExprType().typeFamily == TypeFamily.BOOLEAN) {
          ((ConstExprent) branch1).forceBooleanToInt();
        } else if (branch2 instanceof ConstExprent && branch1.getExprType().typeFamily == TypeFamily.INTEGER
            && branch2.getExprType().typeFamily == TypeFamily.BOOLEAN) {
          ((ConstExprent) branch2).forceBooleanToInt();
        }

        buf.append(condBuf)
          .appendPossibleNewline(" ").append("? ")
          .append(wrapOperandString(lstOperands.get(1), true, indent))
          .appendPossibleNewline(" ").append(": ")
          .append(wrapOperandString(lstOperands.get(2), true, indent));
        buf.popNewlineGroup();
        return buf;
      }
      case INSTANCEOF: {
        TextBuffer instOfLeft = wrapOperandString(lstOperands.get(0), true, indent);
        // RTF: when the left operand's type is provably incompatible with the
        // instanceof target, cast to Object first. javac rejects instanceof on
        // unrelated types but the bytecode is valid.
        if (DecompilerContext.isRoundtripFidelity() && lstOperands.size() >= 2) {
          VarType leftType = lstOperands.get(0).getExprType();
          VarType rightType = lstOperands.get(1).getExprType();
          if (leftType.type == CodeType.OBJECT && rightType.type == CodeType.OBJECT
              && leftType.value != null && rightType.value != null
              && !leftType.value.equals(rightType.value)
              && !"java/lang/Object".equals(leftType.value)) {
            // Check if left is NOT a supertype of right
            boolean compatible = DecompilerContext.getStructContext() != null
                && (DecompilerContext.getStructContext().instanceOf(leftType.value, rightType.value)
                    || DecompilerContext.getStructContext().instanceOf(rightType.value, leftType.value));
            if (!compatible) {
              instOfLeft = instOfLeft.enclose("(Object)", "");
            }
          }
        }
        buf.append(instOfLeft).append(" instanceof ");

        if (this.lstOperands.size() > 2) {
          // Pattern instanceof creation- only happens when we have more than 2 exprents

          Pattern pattern = (Pattern) this.lstOperands.get(2);
          for (VarExprent var : pattern.getPatternVars()) {
            var.setWritingPattern();
          }

          buf.append(wrapOperandString(this.lstOperands.get(2), true, indent));
        } else {
          buf.append(wrapOperandString(lstOperands.get(1), true, indent));
        }


        return buf;
      }
      case LCMP:
      case FCMPL:
      case FCMPG:
      case DCMPL:
      case DCMPG:
        // shouldn't appear in the final code
        return buf.append(wrapOperandString(lstOperands.get(0), true, indent).prepend(funcType.operator + "("))
                 .append(", ")
                 .append(wrapOperandString(lstOperands.get(1), true, indent))
                 .append(")");
    }

    if (funcType.castType != null) {
      // We can't directly cast some object types, so we need to make sure the unboxing happens.
      // The types seem to be inconsistant but there is no harm in forcing the unboxing when not strictly needed.
      // Type   | Works | Doesn't
      // Integer| LFD   | BCS
      // Long   | FD    | I
      // Float  | D     | IL
      // Double |       | ILF
      if (lstOperands.get(0) instanceof InvocationExprent) {
        InvocationExprent inv = (InvocationExprent)lstOperands.get(0);
        if (inv.isUnboxingCall()) {
          inv.forceUnboxing(true);
        }
      }

      if (!needsCast) {
        return buf.append(lstOperands.get(0).toJava(indent));
      }

      return buf.append(ExprProcessor.getTypeName(funcType.castType)).encloseWithParens().append(wrapOperandString(lstOperands.get(0), true, indent));
    }

    //        return "<unknown function>";
    throw new RuntimeException("invalid function");
  }

  // Make sure that any boxing that is required is properly expressed
  /**
   * RTF: check if an expression used in a boolean context (&&, ||) needs != 0.
   * This happens when a variable has int declaration type but boolean inferred type,
   * due to SSA merging widening boolean to int.
   */
  private static boolean needsBoolConversion(Exprent expr) {
    if (expr instanceof VarExprent) {
      VarExprent var = (VarExprent) expr;
      // Dual-typed vars are rendered as 'var' (compiler infers int), so they need conversion
      if (var.getProcessor() != null && var.getProcessor().isDualTypedVar(var.getName())) {
        return true;
      }
      // Variables with boolean LVT type are definitely boolean - no conversion needed
      if (var.getLVT() != null && "Z".equals(var.getLVT().getDescriptor())) {
        return false;
      }
      // Check if the variable processor named it as int (definitive signal)
      String name = var.getName();
      if (name != null && name.startsWith("int")) {
        return true;
      }
      VarType varType = var.getVarType();
      if (varType.typeFamily == TypeFamily.INTEGER && !varType.equals(VarType.VARTYPE_BOOLEAN)) {
        return true;
      }
    }
    // FunctionExprent results that are boolean (comparisons, boolean AND, etc.) don't need conversion
    if (expr instanceof FunctionExprent) {
      FunctionExprent fe = (FunctionExprent) expr;
      if (fe.funcType.isComparison() || fe.funcType == FunctionType.BOOLEAN_AND
          || fe.funcType == FunctionType.BOOLEAN_OR || fe.funcType == FunctionType.BOOL_NOT) {
        return false;
      }
      // AND/OR with a boolean operand produces boolean
      if (fe.funcType == FunctionType.AND || fe.funcType == FunctionType.OR) {
        for (Exprent op : fe.getLstOperands()) {
          if (isBoolishOperand(op)) return false;
        }
      }
    }
    if (expr.getExprType().typeFamily == TypeFamily.INTEGER) {
      return true;
    }
    return false;
  }

  private Exprent unwrapBoxing(Exprent expr) {
    if (expr instanceof InvocationExprent) {
      if (((InvocationExprent) expr).isUnboxingCall()) {
        Exprent inner = ((InvocationExprent) expr).getInstance();
        if (inner instanceof FunctionExprent && ((FunctionExprent)inner).funcType == FunctionType.CAST) {
          inner.addBytecodeOffsets(expr.bytecode);
          expr = inner;
        }
      }
    }

    return expr;
  }

  public void unwrapBox() {
    for (int i = 0; i < this.lstOperands.size(); i++) {
      this.lstOperands.set(i, unwrapBoxing(this.lstOperands.get(i)));
    }
  }

  @Override
  public int getPrecedence() {
    if ((funcType == FunctionType.CAST || funcType.castType != null) && !doesCast()) {
      return lstOperands.get(0).getPrecedence();
    }

    if (funcType == FunctionType.OTHER) {
      throw new PluginImplementationException();
    }

    return funcType.precedence;
  }

  public VarType getSimpleCastType() {
    return funcType.castType;
  }

  protected TextBuffer wrapOperandString(Exprent expr, boolean eq, int indent) {
    return wrapOperandString(expr, eq, indent, false);
  }

  private TextBuffer wrapOperandString(Exprent expr, boolean eq, int indent, boolean newlineGroup) {
    int myprec = getPrecedence();
    int exprprec = expr.getPrecedence();

    boolean parentheses = exprprec > myprec;
    if (!parentheses && eq) {
      parentheses = (exprprec == myprec);
      if (parentheses) {
        if (expr instanceof FunctionExprent &&
            ((FunctionExprent)expr).getFuncType() == funcType) {
          // Float operations are not assocative!
          if (expr.getExprType() != VarType.VARTYPE_FLOAT && expr.getExprType() != VarType.VARTYPE_DOUBLE) {
            // RTF: keep parentheses to preserve original evaluation order.
            // Without parens, a + (b + c) renders as a + b + c, which javac
            // left-associates to (a + b) + c - different bytecode.
            if (DecompilerContext.isRoundtripFidelity()) {
              parentheses = true;  // always keep parens for same-precedence in RTF
            } else {
              parentheses = !ASSOCIATIVITY.contains(funcType);
            }
          }
        }
      }
    }

    if (newlineGroup && !parentheses && myprec == exprprec) {
      if (expr instanceof FunctionExprent) {
        FunctionExprent funcExpr = (FunctionExprent) expr;
        if (funcExpr.getFuncType() == FunctionType.CAST && !funcExpr.doesCast()) {
          Exprent subExpr = funcExpr.getLstOperands().get(0);
          if (subExpr instanceof FunctionExprent) {
            funcExpr = (FunctionExprent) subExpr;
          }
        }
        funcExpr.disableNewlineGroupCreation = true;
      }
    }

    TextBuffer res = expr.toJava(indent);

    if (parentheses) {
      TextBuffer oldRes = res;
      res = new TextBuffer().append("(");
      res.pushNewlineGroup(indent, 1);
      res.appendPossibleNewline();
      res.append(oldRes);
      res.appendPossibleNewline("", true);
      res.popNewlineGroup();
      res.append(")");
    }

    return res;
  }

  private static VarType getMaxVarType(VarType ...arr) {
    for (int i = 0; i < TYPE_PRIMITIVES.length; i++) {
      for (VarType anArr : arr) {
        if (anArr.type == TYPE_PRIMITIVES[i]) {
          return TYPES[i];
        }
      }
    }

    return VarType.VARTYPE_INT;
  }

  // *****************************************************************************
  // getter and setter methods
  // *****************************************************************************

  public FunctionType getFuncType() {
    return funcType;
  }

  public void setFuncType(FunctionType funcType) {
    this.funcType = funcType;
  }

  public List<Exprent> getLstOperands() {
    return lstOperands;
  }

  public void setImplicitType(VarType implicitType) {
    this.implicitType = implicitType;
  }

  public boolean doesCast() {
    return needsCast;
  }

  public void setForceLiteral(boolean forceLiteral) {
    this.forceLiteral = forceLiteral;
  }

  public void setNeedsCast(boolean needsCast) {
    this.needsCast = needsCast;
  }

  public void setInvocationInstance() {
    if (funcType == FunctionType.CAST) {
      lstOperands.get(0).setInvocationInstance();
    }
  }

  @Override
  public void setIsQualifier() {
    if (funcType == FunctionType.CAST && !doesCast()) {
      lstOperands.get(0).setIsQualifier();
    }
  }

  @Override
  public boolean allowNewlineAfterQualifier() {
    if (funcType == FunctionType.CAST && !doesCast()) {
      return lstOperands.get(0).allowNewlineAfterQualifier();
    }
    return super.allowNewlineAfterQualifier();
  }

  @Override
  public void getBytecodeRange(BitSet values) {
    measureBytecode(values, lstOperands);
    measureBytecode(values);
  }

  @Override
  public void processSforms(SFormsConstructor sFormsConstructor, VarMapHolder varMaps, Statement stat, boolean calcLiveVars) {
    switch (this.getFuncType()) {
      case TERNARY: {
        // `a ? b : c`
        // Java language spec: 16.1.5.
        this.getLstOperands().get(0).processSforms(sFormsConstructor, varMaps, stat, calcLiveVars);

        VarMapHolder bVarMaps = VarMapHolder.ofNormal(varMaps.getIfTrue());
        this.getLstOperands().get(1).processSforms(sFormsConstructor, bVarMaps, stat, calcLiveVars);

        // reuse the varMaps for the false branch.
        varMaps.setNormal(varMaps.getIfFalse());
        this.getLstOperands().get(2).processSforms(sFormsConstructor, varMaps, stat, calcLiveVars);

        if (bVarMaps.isNormal() && varMaps.isNormal()) {
          varMaps.mergeNormal(bVarMaps.getNormal());
        } else if (!varMaps.isNormal()) {
          // b and c are boolean expression and at least c had an assignment.
          varMaps.mergeIfTrue(bVarMaps.getIfTrue());
          varMaps.mergeIfFalse(bVarMaps.getIfFalse());
        } else {
          // b and c are boolean expression and at b had an assignment.
          // avoid cloning the c varmap.
          bVarMaps.mergeIfTrue(varMaps.getNormal());
          bVarMaps.mergeIfFalse(varMaps.getNormal());

          varMaps.set(bVarMaps); // move over the maps.
        }

        return;
      }
      case BOOLEAN_AND: {
        // `a && b`
        // Java language spec: 16.1.2.
        this.getLstOperands().get(0).processSforms(sFormsConstructor, varMaps, stat, calcLiveVars);

        varMaps.makeFullyMutable();
        SFormsFastMapDirect ifFalse = varMaps.getIfFalse();
        varMaps.setNormal(varMaps.getIfTrue());

        this.getLstOperands().get(1).processSforms(sFormsConstructor, varMaps, stat, calcLiveVars);
        varMaps.mergeIfFalse(ifFalse);
        return;
      }
      case BOOLEAN_OR: {
        // `a || b`
        // Java language spec: 16.1.3.
        this.getLstOperands().get(0).processSforms(sFormsConstructor, varMaps, stat, calcLiveVars);

        varMaps.makeFullyMutable();
        SFormsFastMapDirect ifTrue = varMaps.getIfTrue();
        varMaps.setNormal(varMaps.getIfFalse());

        this.getLstOperands().get(1).processSforms(sFormsConstructor, varMaps, stat, calcLiveVars);
        varMaps.mergeIfTrue(ifTrue);
        return;
      }
      case BOOL_NOT: {
        // `!a`
        // Java language spec: 16.1.4.
        this.getLstOperands().get(0).processSforms(sFormsConstructor, varMaps, stat, calcLiveVars);
        varMaps.swap();

        return;
      }
      case INSTANCEOF: {
        // `a instanceof B`
        // pattern matching instanceof creates a new variable when true.
        this.getLstOperands().get(0).processSforms(sFormsConstructor, varMaps, stat, calcLiveVars);
        varMaps.toNormal();

        if (this.getLstOperands().size() == 3) {
          // pattern matching
          // `a instanceof B b`
          // pattern matching variables are explained in different parts of the spec,
          // but it comes down to the same ideas.
          varMaps.makeFullyMutable();

          Pattern pattern = (Pattern) this.getLstOperands().get(2);

          for (VarExprent var : pattern.getPatternVars()) {
            sFormsConstructor.updateVarExprent(var, stat, varMaps.getIfTrue(), calcLiveVars);
          }
        }

        return;
      }
      case IMM:
      case MMI:
      case IPP:
      case PPI: {
        // process the var/field/array access
        // Note that ++ and -- are both reads and writes.
        this.getLstOperands().get(0).processSforms(sFormsConstructor, varMaps, stat, calcLiveVars);

        switch (this.getLstOperands().get(0).type) {
          case VAR: {
            VarExprent varExprent = (VarExprent) this.getLstOperands().get(0);

            VarVersionPair phantomPair = sFormsConstructor.getOrCreatePhantom(varExprent.getVarVersionPair());

            // Can't have ++ or -- on a boolean expression.
            varMaps.getNormal().setCurrentVar(phantomPair);
            break;
          }
          case FIELD: {
            // assignment to a field resets all fields.
            // Can't have ++ or -- on a boolean expression.
            varMaps.getNormal().removeAllFields();
            break;
          }
        }
        return;
      }
      default:{
        super.processSforms(sFormsConstructor, varMaps, stat, calcLiveVars);
      }
    }
  }

  // *****************************************************************************
  // IMatchable implementation
  // *****************************************************************************

  @Override
  public boolean match(MatchNode matchNode, MatchEngine engine) {
    if (!super.match(matchNode, engine)) {
      return false;
    }

    FunctionType type = (FunctionType)matchNode.getRuleValue(MatchProperties.EXPRENT_FUNCTYPE);
    return type == null || this.funcType == type;
  }
}
