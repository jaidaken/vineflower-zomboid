// Copyright 2000-2017 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.modules.decompiler.vars;

import org.jetbrains.java.decompiler.code.CodeConstants;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.modules.decompiler.ValidationHelper;
import org.jetbrains.java.decompiler.modules.decompiler.exps.*;
import org.jetbrains.java.decompiler.modules.decompiler.flow.DirectGraph;
import org.jetbrains.java.decompiler.modules.decompiler.stats.*;
import org.jetbrains.java.decompiler.struct.StructClass;
import org.jetbrains.java.decompiler.struct.StructMethod;
import org.jetbrains.java.decompiler.struct.gen.CodeType;
import org.jetbrains.java.decompiler.struct.gen.MethodDescriptor;
import org.jetbrains.java.decompiler.struct.gen.TypeFamily;
import org.jetbrains.java.decompiler.struct.gen.VarType;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

public class VarTypeProcessor {
  public enum FinalType {
    NON_FINAL, EXPLICIT_FINAL, FINAL
  }

  private final StructMethod method;
  private final MethodDescriptor methodDescriptor;
  private final Map<VarVersionPair, VarType> mapExprentMinTypes = new HashMap<>();
  private final Map<VarVersionPair, VarType> mapExprentMaxTypes = new HashMap<>();
  private final Map<VarVersionPair, FinalType> mapFinalVars = new HashMap<>();

  public VarTypeProcessor(StructMethod mt, MethodDescriptor md) {
    method = mt;
    methodDescriptor = md;
  }

  public void calculateVarTypes(RootStatement root, DirectGraph graph) {
    setInitVars(root);

    resetExprentTypes(graph);

    //noinspection StatementWithEmptyBody
    while (!processVarTypes(graph)) ;

    ValidationHelper.validateVars(graph, root, var -> var.getVarType() != VarType.VARTYPE_UNKNOWN, "Var type not set!");
  }

  private void setInitVars(RootStatement root) {
    boolean thisVar = !method.hasModifier(CodeConstants.ACC_STATIC);

    MethodDescriptor md = methodDescriptor;

    if (thisVar) {
      StructClass cl = (StructClass)DecompilerContext.getContextProperty(DecompilerContext.CURRENT_CLASS);
      VarType clType = new VarType(CodeType.OBJECT, 0, cl.qualifiedName);
      mapExprentMinTypes.put(new VarVersionPair(0, 1), clType);
      mapExprentMaxTypes.put(new VarVersionPair(0, 1), clType);
    }

    int varIndex = 0;
    for (int i = 0; i < md.params.length; i++) {
      mapExprentMinTypes.put(new VarVersionPair(varIndex + (thisVar ? 1 : 0), 1), md.params[i]);
      mapExprentMaxTypes.put(new VarVersionPair(varIndex + (thisVar ? 1 : 0), 1), md.params[i]);
      varIndex += md.params[i].stackSize;
    }

    // catch variables
    LinkedList<Statement> stack = new LinkedList<>();
    stack.add(root);

    while (!stack.isEmpty()) {
      Statement stat = stack.removeFirst();

      List<VarExprent> vars = stat.getImplicitlyDefinedVars();

      if (vars != null) {
        for (VarExprent var : vars) {
          mapExprentMinTypes.put(new VarVersionPair(var.getIndex(), 1), var.getVarType());
          mapExprentMaxTypes.put(new VarVersionPair(var.getIndex(), 1), var.getVarType());
        }
      }

      stack.addAll(stat.getStats());
    }
  }

  private static void resetExprentTypes(DirectGraph graph) {
    graph.iterateExprents(exprent -> {
      List<Exprent> lst = exprent.getAllExprents(true);
      lst.add(exprent);

      for (Exprent expr : lst) {
        if (expr instanceof VarExprent) {
          VarExprent ve = (VarExprent)expr;
          if (ve.getLVT() != null) {
            ve.setVarType(ve.getLVT().getVarType());
          } else {
            ve.setVarType(VarType.VARTYPE_UNKNOWN);
          }
        }
        else if (expr instanceof ConstExprent) {
          ConstExprent constExpr = (ConstExprent)expr;
          if (constExpr.getConstType().typeFamily == TypeFamily.INTEGER) {
            constExpr.setConstType(new ConstExprent(constExpr.getIntValue(), constExpr.isBoolPermitted(), null).getConstType());
          }
        }
      }
      return 0;
    });
  }

  private boolean processVarTypes(DirectGraph graph) {
    return graph.iterateExprents(exprent -> checkTypeExprent(exprent) ? 0 : 1);
  }

  // true -> Do nothing
  // false -> cancel iteration
  private boolean checkTypeExprent(Exprent exprent) {
    for (Exprent expr : exprent.getAllExprents(true)) {
      if (!checkTypeExpr(expr)) {
        return false;
      }
    }

    return checkTypeExpr(exprent);
  }

  private boolean checkTypeExpr(Exprent exprent) {
    if (exprent instanceof ConstExprent) {
      ConstExprent constExpr = (ConstExprent) exprent;
      if (constExpr.getConstType().typeFamily.isLesserOrEqual(TypeFamily.INTEGER)) { // boolean or integer
        VarVersionPair pair = new VarVersionPair(constExpr.id, -1);
        if (!mapExprentMinTypes.containsKey(pair)) {
          mapExprentMinTypes.put(pair, constExpr.getConstType());
        }
      }
    }

    CheckTypesResult result = exprent.checkExprTypeBounds();

    boolean res = true;
    if (result != null) {
      for (CheckTypesResult.ExprentTypePair entry : result.getLstMaxTypeExprents()) {
        if (entry.type.typeFamily != TypeFamily.OBJECT) {
          changeExprentType(entry.exprent, entry.type, 1);
        }
      }

      for (CheckTypesResult.ExprentTypePair entry : result.getLstMinTypeExprents()) {
        res &= changeExprentType(entry.exprent, entry.type, 0);
      }
    }
    return res;
  }


  // true -> Do nothing
  // false -> cancel iteration
  private boolean changeExprentType(Exprent exprent, VarType newType, int minMax) {

    switch (exprent.type) {
      case CONST:
        ConstExprent constExpr = (ConstExprent)exprent;
        VarType constType = constExpr.getConstType();

        if (newType.typeFamily.isGreater(TypeFamily.INTEGER) || constType.typeFamily.isGreater(TypeFamily.INTEGER)) {
          return true;
        }
        else if (newType.typeFamily == TypeFamily.INTEGER) {
          VarType minInteger = new ConstExprent((Integer)constExpr.getValue(), false, null).getConstType();
          if (minInteger.isStrictSuperset(newType)) {
            newType = minInteger;
          }
        }
        return changeVarExprentType(exprent, newType, minMax, new VarVersionPair(exprent.id, -1));
      case VAR:
        // In roundtrip fidelity mode, preserve the exact type from the LocalVariableTable.
        // The LVT specifies the original bytecode type (e.g. int), and we should not allow
        // the type processor to narrow it (e.g. to byte) based on usage analysis, because
        // that would change the local variable type upon recompilation.
        if (DecompilerContext.isRoundtripFidelity()) {
          VarExprent varExpr = (VarExprent) exprent;
          if (varExpr.getLVT() != null) {
            VarType lvtType = varExpr.getLVT().getVarType();
            // Pin OBJECT types and INT from LVT. OBJECT pinning prevents wrong reference
            // types. INT pinning prevents Vineflower from narrowing int to byte/short/char
            // when the LVT says int (the original source used int).
            // Don't pin byte/short/char/boolean — those LVT types mean the programmer
            // intended the narrow type.
            if ((lvtType.type == CodeType.OBJECT && !"java/lang/Object".equals(lvtType.value))
                || lvtType.equals(VarType.VARTYPE_INT)) {
              // Don't pin java/lang/Object — it's too generic (usually from erased generics).
              // Let VF's type inference recover the real type from usage context.
              // Don't pin if the proposed type is incompatible with the LVT type.
              // This handles variables reassigned to different subtypes (e.g., a variable
              // declared as IsoWindow in LVT but also assigned from IsoThumpable).
              if (newType.type == CodeType.OBJECT && newType.value != null && lvtType.value != null
                  && !newType.value.equals(lvtType.value)) {
                boolean compatible = DecompilerContext.getStructContext() != null
                    && DecompilerContext.getStructContext().instanceOf(newType.value, lvtType.value);
                if (!compatible) {
                  // Fall through to normal type processing — the variable needs a wider type
                  return changeVarExprentType(exprent, newType, minMax, new VarVersionPair(varExpr));
                }
              }
              VarVersionPair varPair = new VarVersionPair(varExpr);
              mapExprentMinTypes.put(varPair, lvtType);
              mapExprentMaxTypes.put(varPair, lvtType);
              return true;
            }
          }
        }
        return changeVarExprentType(exprent, newType, minMax, new VarVersionPair((VarExprent) exprent));

      case ASSIGNMENT:
        return changeExprentType(((AssignmentExprent)exprent).getRight(), newType, minMax);

      case FUNCTION:
        return changeFunctionExprentType(newType, minMax, (FunctionExprent)exprent);
      case SWITCH:
        return changeSwitchExprentType(newType, minMax, (SwitchExprent) exprent);
    }

    return true;
  }

  private boolean changeVarExprentType(Exprent exprent, VarType newType, int minMax, VarVersionPair pair) {
    if (minMax == 0) { // min
      VarType currentMinType = mapExprentMinTypes.get(pair);
      VarType newMinType;
      if (currentMinType == null || newType.typeFamily.isGreater(currentMinType.typeFamily)) {
        newMinType = newType;
      } else if (newType.typeFamily.isLesser(currentMinType.typeFamily)) {
        return true;
      } else {
        newMinType = VarType.getCommonSupertype(currentMinType, newType);
      }

      mapExprentMinTypes.put(pair, newMinType);
      if (exprent instanceof ConstExprent) {
        ((ConstExprent) exprent).setConstType(newMinType);
      }

      if (currentMinType != null && (newMinType.typeFamily.isGreater(currentMinType.typeFamily) || newMinType.isStrictSuperset(currentMinType))) {
        return false;
      }
    } else {  // max
      VarType currentMaxType = mapExprentMaxTypes.get(pair);
      VarType newMaxType;
      if (currentMaxType == null || newType.typeFamily.isLesser(currentMaxType.typeFamily)) {
        newMaxType = newType;
      } else if (newType.typeFamily.isGreater(currentMaxType.typeFamily)) {
        return true;
      } else {
        newMaxType = VarType.getCommonMinType(currentMaxType, newType);
      }

      mapExprentMaxTypes.put(pair, newMaxType);
    }
    return true;
  }

  private boolean changeFunctionExprentType(VarType newType, int minMax, FunctionExprent func) {
    int offset = 0;
    switch (func.getFuncType()) {
      case TERNARY:   // FIXME:
        offset++;
      case AND:
      case OR:
      case XOR:
        return changeExprentType(func.getLstOperands().get(offset), newType, minMax) &
               changeExprentType(func.getLstOperands().get(offset + 1), newType, minMax);
    }
    return true;
  }

  private boolean changeSwitchExprentType(VarType newType, int minMax, SwitchExprent switchExpr) {
    if (minMax == 1) { // max
      VarType type = switchExpr.getExprType();
      if (newType.typeFamily == TypeFamily.INTEGER && type.typeFamily == newType.typeFamily) {
        switchExpr.setType(newType);
      }
    }
    return true;
  }

  public Map<VarVersionPair, VarType> getMapExprentMaxTypes() {
    return mapExprentMaxTypes;
  }

  public Map<VarVersionPair, VarType> getMapExprentMinTypes() {
    return mapExprentMinTypes;
  }

  public Map<VarVersionPair, FinalType> getMapFinalVars() {
    return mapFinalVars;
  }

  public void setVarType(VarVersionPair pair, VarType type) {
    mapExprentMinTypes.put(pair, type);
  }

  public VarType getVarType(VarVersionPair pair) {
    return mapExprentMinTypes.get(pair);
  }

  /**
   * RTF post-pass: narrow Object-typed variables to their actual usage type.
   * Runs after type inference stabilizes (which leaves erased generics as Object).
   * Scans all assignments to Object variables and narrows based on RHS type.
   * Only narrows when ALL assignments to the variable produce the same specific type.
   */
  public static void narrowObjectTypes(Statement root, VarProcessor varProc) {
    Map<VarVersionPair, VarType> minTypes = varProc.getVarVersions().getTypeProcessor().getMapExprentMinTypes();

    // Collect all assignments to Object-typed variables
    Map<Integer, List<VarType>> varAssignTypes = new HashMap<>();
    collectAssignmentTypes(root, minTypes, varAssignTypes);

    // For each variable that's currently Object, check if all assignments produce
    // the same more specific type
    for (Map.Entry<Integer, List<VarType>> entry : varAssignTypes.entrySet()) {
      int varIndex = entry.getKey();
      List<VarType> types = entry.getValue();

      VarVersionPair pair = new VarVersionPair(varIndex, 0);
      VarType currentType = minTypes.get(pair);
      if (currentType == null || !"java/lang/Object".equals(currentType.value)) {
        continue; // not Object, skip
      }

      // Find the common non-Object type across all assignments
      VarType narrowedType = null;
      boolean canNarrow = true;
      for (VarType t : types) {
        if (t == null || "java/lang/Object".equals(t.value)) {
          continue; // skip Object assignments (e.g., null init)
        }
        if (narrowedType == null) {
          narrowedType = t;
        } else if (!narrowedType.value.equals(t.value)) {
          // Different types assigned - find common supertype
          VarType common = VarType.getCommonSupertype(narrowedType, t);
          if (common == null || "java/lang/Object".equals(common.value)) {
            canNarrow = false;
            break;
          }
          narrowedType = common;
        }
      }

      if (canNarrow && narrowedType != null && !"java/lang/Object".equals(narrowedType.value)) {
        minTypes.put(pair, narrowedType);
      }
    }
  }

  private static void collectAssignmentTypes(Statement stat, Map<VarVersionPair, VarType> minTypes,
                                              Map<Integer, List<VarType>> varAssignTypes) {
    if (stat.getExprents() != null) {
      for (Exprent expr : stat.getExprents()) {
        collectAssignmentTypesFromExpr(expr, minTypes, varAssignTypes);
      }
    }

    for (Statement st : stat.getStats()) {
      collectAssignmentTypes(st, minTypes, varAssignTypes);
    }

    // Also check var definitions
    for (Exprent expr : stat.getVarDefinitions()) {
      collectAssignmentTypesFromExpr(expr, minTypes, varAssignTypes);
    }

  }

  private static void collectAssignmentTypesFromExpr(Exprent expr, Map<VarVersionPair, VarType> minTypes,
                                                      Map<Integer, List<VarType>> varAssignTypes) {
    if (expr instanceof AssignmentExprent) {
      AssignmentExprent assign = (AssignmentExprent) expr;
      if (assign.getLeft() instanceof VarExprent) {
        VarExprent var = (VarExprent) assign.getLeft();
        int index = var.getIndex();
        VarVersionPair pair = new VarVersionPair(index, 0);
        VarType currentType = minTypes.get(pair);
        if (currentType != null && "java/lang/Object".equals(currentType.value)) {
          VarType rhsType = assign.getRight().getExprType();
          varAssignTypes.computeIfAbsent(index, k -> new ArrayList<>()).add(rhsType);
        }
      }
    }

    // Recurse into sub-expressions (for nested assignments in ternaries, etc.)
    for (Exprent sub : expr.getAllExprents()) {
      collectAssignmentTypesFromExpr(sub, minTypes, varAssignTypes);
    }
  }
}