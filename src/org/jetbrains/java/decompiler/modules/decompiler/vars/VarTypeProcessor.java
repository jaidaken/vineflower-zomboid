// Copyright 2000-2017 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.modules.decompiler.vars;

import org.jetbrains.java.decompiler.code.CodeConstants;
import org.jetbrains.java.decompiler.main.ClassesProcessor.ClassNode;
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
import org.jetbrains.java.decompiler.struct.gen.generics.GenericType;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

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

      // RTF: strip generic types that would cause compilation errors.
      if (DecompilerContext.isRoundtripFidelity() && newMinType != null) {
        boolean shouldStrip = VarType.hasObjectOrGenvarArgs(newMinType);
        // Also strip when inside a generic class and the type has concrete args
        // that are likely call-site substitutions for type variables.
        if (!shouldStrip && newMinType.isGeneric()
            && newMinType instanceof org.jetbrains.java.decompiler.struct.gen.generics.GenericType) {
          ClassNode currCls = DecompilerContext.getContextProperty(DecompilerContext.CURRENT_CLASS_NODE);
          if (currCls != null && currCls.classStruct.getSignature() != null
              && !currCls.classStruct.getSignature().fparameters.isEmpty()) {
            for (VarType arg : ((org.jetbrains.java.decompiler.struct.gen.generics.GenericType) newMinType).getArguments()) {
              if (arg.type == CodeType.OBJECT && arg.value != null
                  && !"java/lang/Object".equals(arg.value)
                  && arg.type != CodeType.GENVAR) {
                // Concrete class arg inside a generic class — likely over-resolved
                shouldStrip = true;
                break;
              }
            }
          }
        }
        if (shouldStrip) {
          newMinType = new VarType(newMinType.type, newMinType.arrayDim, newMinType.value);
        }
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

    // Collect for-each variable indices — don't narrow these since they need var
    Set<Integer> forEachVars = new HashSet<>();
    collectForEachVars(root, forEachVars);

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
      if (forEachVars.contains(varIndex)) {
        continue; // don't narrow for-each vars — they need var for raw collections
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
        } else if (narrowedType.value == null || !narrowedType.value.equals(t.value)) {
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

  /**
   * Collect usage-based type info for Object-typed variables.
   * When a variable is used as the instance of a method call or field access,
   * the declaring class of that method/field tells us the real type.
   */
  private static void collectUsageTypes(Statement stat, Map<VarVersionPair, VarType> minTypes,
                                         Map<Integer, List<VarType>> varAssignTypes) {
    collectUsageTypesFromStat(stat, minTypes, varAssignTypes);
  }

  private static void collectUsageTypesFromStat(Statement stat, Map<VarVersionPair, VarType> minTypes,
                                                 Map<Integer, List<VarType>> varAssignTypes) {
    if (stat.getExprents() != null) {
      for (Exprent expr : stat.getExprents()) {
        collectUsageTypesFromExpr(expr, minTypes, varAssignTypes);
      }
    }
    for (Exprent expr : stat.getVarDefinitions()) {
      collectUsageTypesFromExpr(expr, minTypes, varAssignTypes);
    }
    for (Statement st : stat.getStats()) {
      collectUsageTypesFromStat(st, minTypes, varAssignTypes);
    }
  }

  private static void collectUsageTypesFromExpr(Exprent expr, Map<VarVersionPair, VarType> minTypes,
                                                 Map<Integer, List<VarType>> varAssignTypes) {
    // Check if this is a method call on an Object-typed variable
    if (expr instanceof InvocationExprent) {
      InvocationExprent invoc = (InvocationExprent) expr;
      Exprent inst = invoc.getInstance();
      if (inst instanceof VarExprent) {
        VarExprent var = (VarExprent) inst;
        VarVersionPair pair = new VarVersionPair(var.getIndex(), 0);
        VarType currentType = minTypes.get(pair);
        if (currentType != null && "java/lang/Object".equals(currentType.value)) {
          // The variable is Object but used as instance for a method call.
          // The method's declaring class is the real type.
          String className = invoc.getClassname();
          if (className != null && !"java/lang/Object".equals(className)) {
            varAssignTypes.computeIfAbsent(var.getIndex(), k -> new ArrayList<>())
                .add(new VarType(CodeType.OBJECT, 0, className));
          }
        }
      }
    }
    // Check field access on Object-typed variable
    if (expr instanceof FieldExprent) {
      FieldExprent field = (FieldExprent) expr;
      Exprent inst = field.getInstance();
      if (inst instanceof VarExprent) {
        VarExprent var = (VarExprent) inst;
        VarVersionPair pair = new VarVersionPair(var.getIndex(), 0);
        VarType currentType = minTypes.get(pair);
        if (currentType != null && "java/lang/Object".equals(currentType.value)) {
          String className = field.getClassname();
          if (className != null && !"java/lang/Object".equals(className)) {
            varAssignTypes.computeIfAbsent(var.getIndex(), k -> new ArrayList<>())
                .add(new VarType(CodeType.OBJECT, 0, className));
          }
        }
      }
    }
    // Recurse
    for (Exprent sub : expr.getAllExprents()) {
      collectUsageTypesFromExpr(sub, minTypes, varAssignTypes);
    }
  }

  private static void collectForEachVars(Statement stat, Set<Integer> forEachVars) {
    if (stat instanceof DoStatement) {
      DoStatement doStat = (DoStatement) stat;
      if (doStat.getLooptype() == DoStatement.Type.FOR_EACH && doStat.getInitExprent() instanceof VarExprent) {
        forEachVars.add(((VarExprent) doStat.getInitExprent()).getIndex());
      }
    }
    for (Statement st : stat.getStats()) {
      collectForEachVars(st, forEachVars);
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

  /**
   * RTF post-pass: upgrade raw collection variable types to generic types
   * based on lambda parameter types from bootstrap args.
   *
   * When a raw collection (e.g., HashSet) is used with a typed lambda
   * (e.g., forEach with IsoChunk parameter), the original code had generic
   * types (HashSet&lt;IsoChunk&gt;) but VF can't recover them from LVT alone.
   * This pass uses the lambda's SAM/instantiated descriptors to derive
   * the generic type parameters and upgrade the variable's type.
   */
  public static void upgradeRawCollectionTypes(Statement root, VarProcessor varProc) {
    Map<VarVersionPair, VarType> minTypes = varProc.getVarVersions().getTypeProcessor().getMapExprentMinTypes();
    Map<Integer, GenericType> upgrades = new HashMap<>();
    collectLambdaGenericTypes(root, minTypes, upgrades);

    for (Map.Entry<Integer, GenericType> entry : upgrades.entrySet()) {
      VarVersionPair pair = new VarVersionPair(entry.getKey(), 0);
      minTypes.put(pair, entry.getValue());
    }
  }

  private static void collectLambdaGenericTypes(Statement stat, Map<VarVersionPair, VarType> minTypes,
                                                 Map<Integer, GenericType> upgrades) {
    if (stat.getExprents() != null) {
      for (Exprent expr : stat.getExprents()) {
        collectLambdaGenericTypesFromExpr(expr, minTypes, upgrades);
      }
    }
    for (Exprent expr : stat.getVarDefinitions()) {
      collectLambdaGenericTypesFromExpr(expr, minTypes, upgrades);
    }
    for (Statement st : stat.getStats()) {
      collectLambdaGenericTypes(st, minTypes, upgrades);
    }
  }

  private static void collectLambdaGenericTypesFromExpr(Exprent expr, Map<VarVersionPair, VarType> minTypes,
                                                         Map<Integer, GenericType> upgrades) {
    // Look for method calls with lambda arguments on raw collection variables
    if (expr instanceof InvocationExprent) {
      InvocationExprent invoc = (InvocationExprent) expr;
      Exprent inst = invoc.getInstance();
      if (inst instanceof VarExprent) {
        VarExprent var = (VarExprent) inst;
        VarVersionPair pair = new VarVersionPair(var.getIndex(), 0);
        VarType currentType = minTypes.get(pair);
        // Only upgrade raw (non-generic) collection types
        if (currentType != null && currentType.type == CodeType.OBJECT
            && !(currentType instanceof GenericType)) {
          for (Exprent param : invoc.getLstParameters()) {
            checkLambdaParam(param, var.getIndex(), currentType, upgrades);
          }
        }
      }
    }
    // Recurse into sub-expressions
    for (Exprent sub : expr.getAllExprents()) {
      collectLambdaGenericTypesFromExpr(sub, minTypes, upgrades);
    }
  }

  private static void checkLambdaParam(Exprent param, int varIndex, VarType collectionType,
                                         Map<Integer, GenericType> upgrades) {
    if (!(param instanceof NewExprent) || !((NewExprent) param).isLambda()) {
      return;
    }
    ClassNode lambdaNode = DecompilerContext.getClassProcessor()
        .getMapRootClasses().get(((NewExprent) param).getNewType().value);
    if (lambdaNode == null || lambdaNode.lambdaInformation == null
        || lambdaNode.lambdaInformation.sam_method_descriptor == null) {
      return;
    }
    MethodDescriptor mdSam = MethodDescriptor.parseDescriptor(
        lambdaNode.lambdaInformation.sam_method_descriptor);
    MethodDescriptor mdInst = MethodDescriptor.parseDescriptor(
        lambdaNode.lambdaInformation.method_descriptor);

    // Collect specific types from lambda params where SAM has Object
    // but instantiated has specific type (generic-dependent params)
    List<VarType> genericArgs = new ArrayList<>();
    Set<String> seen = new java.util.LinkedHashSet<>();
    boolean hasGenericParam = false;
    for (int i = 0; i < mdInst.params.length && i < mdSam.params.length; i++) {
      if ("java/lang/Object".equals(mdSam.params[i].value)
          && mdInst.params[i].type == CodeType.OBJECT
          && !"java/lang/Object".equals(mdInst.params[i].value)) {
        hasGenericParam = true;
        String argValue = mdInst.params[i].value;
        if (seen.add(argValue)) {
          genericArgs.add(mdInst.params[i]);
        }
      }
    }

    if (hasGenericParam && !genericArgs.isEmpty()) {
      // Verify the collection class actually has generic type parameters
      StructClass collCls = DecompilerContext.getStructContext().getClass(collectionType.value);
      if (collCls == null || collCls.getSignature() == null
          || collCls.getSignature().fparameters.isEmpty()) {
        return; // class has no type parameters — can't add generic args
      }
      // Don't add more generic args than the class has type parameters
      int maxArgs = collCls.getSignature().fparameters.size();
      if (genericArgs.size() > maxArgs) {
        genericArgs = genericArgs.subList(0, maxArgs);
      }
      // Don't override if already upgraded with a different type
      if (!upgrades.containsKey(varIndex)) {
        GenericType gt = new GenericType(CodeType.OBJECT, 0,
            collectionType.value, null, genericArgs, GenericType.WILDCARD_NO);
        upgrades.put(varIndex, gt);
      }
    }
  }
}