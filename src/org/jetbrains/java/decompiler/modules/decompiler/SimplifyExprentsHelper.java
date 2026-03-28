// Copyright 2000-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.modules.decompiler;

import org.jetbrains.java.decompiler.code.CodeConstants;
import org.jetbrains.java.decompiler.main.ClassesProcessor.ClassNode;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.extern.IFernflowerPreferences;
import org.jetbrains.java.decompiler.main.rels.ClassWrapper;
import org.jetbrains.java.decompiler.modules.decompiler.exps.*;
import org.jetbrains.java.decompiler.modules.decompiler.exps.FunctionExprent.FunctionType;
import org.jetbrains.java.decompiler.modules.decompiler.sforms.SSAConstructorSparseEx;
import org.jetbrains.java.decompiler.modules.decompiler.stats.BasicBlockStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.IfStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.Statement;
import org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair;
import org.jetbrains.java.decompiler.struct.StructClass;
import org.jetbrains.java.decompiler.struct.gen.CodeType;
import org.jetbrains.java.decompiler.struct.gen.VarType;
import org.jetbrains.java.decompiler.struct.match.MatchEngine;
import org.jetbrains.java.decompiler.util.collections.FastSparseSetFactory.FastSparseSet;
import org.jetbrains.java.decompiler.util.InterpreterUtil;
import org.jetbrains.java.decompiler.util.Pair;

import java.util.*;
import java.util.Map.Entry;

public class SimplifyExprentsHelper {
  @SuppressWarnings("SpellCheckingInspection")
  private static final MatchEngine class14Builder = new MatchEngine(
    "statement type:if iftype:if exprsize:-1",
    " exprent position:head type:if",
    "  exprent type:function functype:eq",
    "   exprent type:field name:$fieldname$",
    "   exprent type:constant consttype:null",
    " statement type:basicblock",
    "  exprent position:-1 type:assignment ret:$assignfield$",
    "   exprent type:var index:$var$",
    "   exprent type:field name:$fieldname$",
    " statement type:sequence statsize:2",
    "  statement type:trycatch",
    "   statement type:basicblock exprsize:1",
    "    exprent type:assignment",
    "     exprent type:var index:$var$",
    "     exprent type:invocation invclass:java/lang/Class signature:forName(Ljava/lang/String;)Ljava/lang/Class;",
    "      exprent position:0 type:constant consttype:string constvalue:$classname$",
    "   statement type:basicblock exprsize:1",
    "    exprent type:exit exittype:throw",
    "  statement type:basicblock exprsize:1",
    "   exprent type:assignment",
    "    exprent type:field name:$fieldname$ ret:$field$",
    "    exprent type:var index:$var$"
  );

  public static boolean simplifyStackVarsStatement(
    Statement stat,
    Set<Integer> setReorderedIfs,
    SSAConstructorSparseEx ssa,
    StructClass cl,
    boolean firstInvocation
  ) {
    boolean res = false;

    List<Exprent> expressions = stat.getExprents();
    if (expressions == null) {
      boolean processClass14 = DecompilerContext.getOption(IFernflowerPreferences.DECOMPILE_CLASS_1_4);

      while (true) {
        boolean changed = false;

        for (Statement st : stat.getStats()) {
          res |= simplifyStackVarsStatement(st, setReorderedIfs, ssa, cl, firstInvocation);

          changed = IfHelper.mergeIfs(st, setReorderedIfs) ||  // collapse composed if's
                    buildIff(st, ssa) ||  // collapse iff ?: statement
                    processClass14 && collapseInlinedClass14(st);  // collapse inlined .class property in version 1.4 and before

          if (changed) {
            break;
          }

          if (!st.getStats().isEmpty() && hasQualifiedNewGetClass(st, st.getStats().get(0))) {
            break;
          }
        }

        res |= changed;

        if (!changed) {
          break;
        }
      }
    } else {
      res = simplifyStackVarsExprents(expressions, cl, stat, firstInvocation);
    }

    return res;
  }

  private static boolean simplifyStackVarsExprents(List<Exprent> list, StructClass cl, Statement stat, boolean firstInvocation) {
    boolean res = false;

    int index = 0;
    while (index < list.size()) {
      Exprent current = list.get(index);

      Exprent ret = isSimpleConstructorInvocation(current);
      if (ret != null) {
        list.set(index, ret);
        res = true;
        continue;
      }

      // lambda expression (Java 8)
      ret = isLambda(current, cl);
      if (ret != null) {
        list.set(index, ret);
        res = true;
        continue;
      }

      // remove monitor exit
      if (isMonitorExit(current)) {
        list.remove(index);
        res = true;
        continue;
      }

      // trivial assignment of a stack variable
      if (isTrivialStackAssignment(current)) {
        list.remove(index);
        res = true;
        continue;
      }

      if (index == list.size() - 1) {
        break;
      }

      Exprent next = list.get(index + 1);

      if (index > 0) {
        Exprent prev = list.get(index - 1);

        if (isSwapConstructorInvocation(prev, current, next)) {
          list.remove(index - 1);
          list.remove(index);
          res = true;
          continue;
        }
      }

      if (isAssignmentReturn(current, next, stat)) {
        list.remove(index);
        res = true;
        continue;
      }

//      if (isMethodArrayAssign(current, next)) {
//        list.remove(index);
//        res = true;
//        continue;
//      }

      // constructor invocation
      if (isConstructorInvocationRemote(list, index)) {
        list.remove(index);
        res = true;
        continue;
      }

      // remove getClass() invocation, which is part of a qualified new
      if (DecompilerContext.getOption(IFernflowerPreferences.REMOVE_GET_CLASS_NEW)) {
        if (isQualifiedNewGetClass(current, next)) {
          list.remove(index);
          res = true;
          continue;
        }
      }

      // direct initialization of an array
      int arrCount = isArrayInitializer(list, index);
      if (arrCount > 0) {
        for (int i = 0; i < arrCount; i++) {
          list.remove(index + 1);
        }
        res = true;
        continue;
      }

      // add array initializer expression
      if (addArrayInitializer(current, next)) {
        list.remove(index + 1);
        res = true;
        continue;
      }

      // integer ++expr and --expr  (except for vars!)
      // In RTF mode, preserve the original evaluation order by skipping these conversions
      if (!DecompilerContext.isRoundtripFidelity()) {
        Exprent func = isPPIorMMI(current);
        if (func != null) {
          list.set(index, func);
          res = true;
          continue;
        }

        // expr++ and expr--
        if (isIPPorIMM(current, next) || isIPPorIMM2(current, next)) {
          list.remove(index + 1);
          res = true;
          continue;
        }
      } else {
        // RTF mode: selectively allow post-increment for array index patterns.
        // Pattern: copy = idx; ++idx; arr[copy] = val  (isIPPorIMM after PPandMMHelper)
        //     or:  copy = idx; idx = copy + 1; arr[copy] = val  (isIPPorIMM2)
        // Safe when the copy variable is a stack var used only as an array index,
        // because stack vars won't be incorrectly merged with real vars during
        // version merging (see FIXME in VarVersionsProcessor.java).
        if (isRTFSafePostIncrement(current, next, list, index)) {
          if (isIPPorIMM(current, next) || isIPPorIMM2(current, next)) {
            list.remove(index + 1);
            res = true;
            continue;
          }
        }
        // RTF: fold 3-statement pattern: copy = field; field = field + 1; return (cast)copy
        // into: return (cast)(field++)
        // Handles the self-increment case where isIPPorIMM2 doesn't match because
        // the increment uses the field directly (field = field + 1) not the copy (field = copy + 1).
        if (index + 2 < list.size() && foldFieldPostIncrementReturn(list, index)) {
          res = true;
          continue;
        }
        // RTF: fold array element self-increment + usage pattern:
        //   arr[idx] = arr[idx] + 1;  target[arr[idx]] = val;
        // into: target[arr[idx]++] = val;
        // Fixes semantic bug: decompiled code reads post-increment value,
        // but original bytecode (dup2/dup_x2) used pre-increment value.
        if (foldArrayElementSelfIncrement(current, next)) {
          list.remove(index);
          res = true;
          continue;
        }
      }

      // assignment on stack
      if (isStackAssignment(current, next)) {
        list.remove(index + 1);
        res = true;
        continue;
      }

      // RTF: chain consecutive assignments with same RHS into a = b = value.
      // javac compiles chained assignments with dup, matching the original bytecode.
      // DISABLED: causes cascading regressions - needs deeper investigation
      // if (DecompilerContext.isRoundtripFidelity() && isChainableAssignment(current, next)) {
      //   list.remove(index + 1);
      //   res = true;
      //   continue;
      // }

      if (!firstInvocation && isStackAssignment2(current, next)) {
        list.remove(index + 1);
        res = true;
        continue;
      }

      // In RTF mode, skip inlining PPI/MMI to preserve original operand order
      if (!DecompilerContext.isRoundtripFidelity() && firstInvocation && inlinePPIAndMMI(current, next)) {
        list.remove(index);
        res = true;
        continue;
      }

      index++;
    }

    return res;
  }

  private static boolean addArrayInitializer(Exprent first, Exprent second) {
    if (first instanceof AssignmentExprent) {
      AssignmentExprent as = (AssignmentExprent) first;

      if (as.getRight() instanceof NewExprent && as.getLeft() instanceof VarExprent) {
        NewExprent newExpr = (NewExprent) as.getRight();

        if (!newExpr.getLstArrayElements().isEmpty()) {
          VarExprent arrVar = (VarExprent) as.getLeft();

          if (second instanceof AssignmentExprent) {
            AssignmentExprent aas = (AssignmentExprent) second;
            if (aas.getLeft() instanceof ArrayExprent) {
              ArrayExprent arrExpr = (ArrayExprent) aas.getLeft();
              if (arrExpr.getArray() instanceof VarExprent &&
                  arrVar.equals(arrExpr.getArray()) &&
                  arrExpr.getIndex() instanceof ConstExprent) {
                int constValue = ((ConstExprent) arrExpr.getIndex()).getIntValue();

                if (constValue < newExpr.getLstArrayElements().size()) {
                  Exprent init = newExpr.getLstArrayElements().get(constValue);
                  if (init instanceof ConstExprent) {
                    ConstExprent cinit = (ConstExprent) init;
                    VarType arrType = newExpr.getNewType().decreaseArrayDim();
                    ConstExprent defaultVal = ExprProcessor.getDefaultArrayValue(arrType);

                    if (cinit.equals(defaultVal)) {
                      Exprent tempExpr = aas.getRight();

                      if ((tempExpr.getExprentUse() & Exprent.SIDE_EFFECTS_FREE) == 0){
                        for (int i = constValue + 1; i < newExpr.getLstArrayElements().size(); i++) {
                          final Exprent exprent = newExpr.getLstArrayElements().get(i);
                          if ((exprent.getExprentUse() & Exprent.SIDE_EFFECTS_FREE) == 0){
                            // can't reorder non-side-effect free expressions
                            return false;
                          }
                        }
                      }

                      if (!tempExpr.containsExprent(arrVar)) {
                        newExpr.getLstArrayElements().set(constValue, tempExpr);

                        if (tempExpr instanceof NewExprent) {
                          NewExprent tempNewExpr = (NewExprent) tempExpr;
                          int dims = newExpr.getNewType().arrayDim;
                          if (dims > 1 && !tempNewExpr.getLstArrayElements().isEmpty()) {
                            tempNewExpr.setDirectArrayInit(true);
                          }
                        }

                        return true;
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }

    return false;
  }

  private static int isArrayInitializer(List<Exprent> list, int index) {
    Exprent current = list.get(index);
    if (current instanceof AssignmentExprent) {
      AssignmentExprent as = (AssignmentExprent) current;

      if (as.getRight() instanceof NewExprent && as.getLeft() instanceof VarExprent) {
        NewExprent newExpr = (NewExprent) as.getRight();

        if (newExpr.getExprType().arrayDim > 0 && newExpr.getLstDims().size() == 1 && newExpr.getLstArrayElements().isEmpty() &&
            newExpr.getLstDims().get(0) instanceof ConstExprent) {

          int size = (Integer) ((ConstExprent) newExpr.getLstDims().get(0)).getValue();
          if (size == 0) {
            return 0;
          }

          VarExprent arrVar = (VarExprent) as.getLeft();
          Map<Integer, Exprent> mapInit = new HashMap<>();

          int i = 1;
          int lastImpure = -1;
          while (index + i < list.size() && i <= size) {
            Exprent expr = list.get(index + i);
            if (expr instanceof AssignmentExprent) {
              AssignmentExprent aas = (AssignmentExprent) expr;
              if (aas.getLeft() instanceof ArrayExprent) {
                ArrayExprent arrExpr = (ArrayExprent) aas.getLeft();
                if (arrExpr.getArray() instanceof VarExprent && arrVar.equals(arrExpr.getArray()) &&
                    arrExpr.getIndex() instanceof ConstExprent) {
                  // TODO: check for a number type. Failure extremely improbable, but nevertheless...
                  int constValue = ((ConstExprent) arrExpr.getIndex()).getIntValue();
                  if (constValue < size && !mapInit.containsKey(constValue)) {
                    if ((aas.getRight().getExprentUse() & Exprent.SIDE_EFFECTS_FREE) == 0) {
                      if(constValue < lastImpure) {
                        // can't reorder non-side-effect free expressions
                        break;
                      }
                      lastImpure = constValue;
                    }
                    if (!aas.getRight().containsExprent(arrVar)) {
                      mapInit.put(constValue, aas.getRight());
                      i++;
                      continue;
                    }
                  }
                }
              }
            }
            break;
          }

          double fraction = ((double) mapInit.size()) / size;

          if ((arrVar.isStack() && fraction > 0) || (size <= 7 && fraction >= 0.3) || (size > 7 && fraction >= 0.7)) {
            List<Exprent> lstRet = new ArrayList<>();

            VarType arrayType = newExpr.getNewType().decreaseArrayDim();
            ConstExprent defaultVal = ExprProcessor.getDefaultArrayValue(arrayType);
            for (int j = 0; j < size; j++) {
              lstRet.add(defaultVal.copy());
            }

            int dims = newExpr.getNewType().arrayDim;
            for (Entry<Integer, Exprent> ent : mapInit.entrySet()) {
              Exprent tempExpr = ent.getValue();
              lstRet.set(ent.getKey(), tempExpr);

              if (tempExpr instanceof NewExprent) {
                NewExprent tempNewExpr = (NewExprent) tempExpr;
                if (dims > 1 && !tempNewExpr.getLstArrayElements().isEmpty()) {
                  tempNewExpr.setDirectArrayInit(true);
                }
              }
            }

            newExpr.setLstArrayElements(lstRet);

            return mapInit.size();
          }
        }
      }
    }

    return 0;
  }

  /*
   * Check for the following pattern:
   * var1 = xxx;
   * return var1;
   * Where var1 is not a stack variable.
   * Turn it into:
   * return xxx;
   *
   * Note that this is transformation will result into java that is less like the original.
   * TODO: put this behind a compiler option.
   */
  private static boolean isAssignmentReturn(Exprent first, Exprent second, Statement stat) {
    //If assignment then exit.
    if (first instanceof AssignmentExprent
        && second instanceof ExitExprent) {
      AssignmentExprent assignment = (AssignmentExprent) first;
      ExitExprent exit = (ExitExprent) second;
      //if simple assign and exit is return and return isn't void
      if (assignment.getCondType() == null
          && exit.getExitType() == ExitExprent.Type.RETURN
          && exit.getValue() != null
          && assignment.getLeft() instanceof VarExprent assignmentLeft
          && exit.getValue() instanceof VarExprent exitValue) {
        //If the assignment before the return is immediately used in the return, inline it.
        if (assignmentLeft.equals(exitValue) && !assignmentLeft.isStack() && !exitValue.isStack()) {
          // Avoid doing this transform for potential pattern matches, as they should be processed by the pattern matcher first.
          if (stat.getTopParent().mt.getBytecodeVersion().hasIfPatternMatching()
            && stat.getParent() instanceof IfStatement ifst && !ifst.isPatternMatched() && stat.getExprents().indexOf(first) == 0
            && assignment.getRight() instanceof FunctionExprent func && func.getFuncType() == FunctionType.CAST
            // Most expensive, do it last
            && ifst.getHeadexprent().getAllExprents(true, false).stream().anyMatch(e -> e instanceof FunctionExprent f && f.getFuncType() == FunctionType.INSTANCEOF)
          ) {
            return false;
          }

          exit.replaceExprent(exitValue, assignment.getRight());
          return true;
        }
      }
    }
    return false;
  }

  /*
   * remove assignments of the form:
   * var10001 = var10001;
   */
  private static boolean isTrivialStackAssignment(Exprent first) {
    if (first instanceof AssignmentExprent) {
      AssignmentExprent asf = (AssignmentExprent) first;

      if (isStackVar(asf.getLeft()) && isStackVar(asf.getRight())) {
        VarExprent left = (VarExprent) asf.getLeft();
        VarExprent right = (VarExprent) asf.getRight();
        return left.getIndex() == right.getIndex();
      }
    }

    return false;
  }

  /*
   * Check for the following pattern:
   * var10001 = xxx;
   * yyy = var10001;
   * and replace it with:
   * var10001 = yyy = xxx;
   *
   * TODO: shouldn't this check if var10001 is used in `yyy`?
   */
  private static boolean isStackAssignment2(Exprent first, Exprent second) {  // e.g. 1.4-style class invocation
    if (first instanceof AssignmentExprent && second instanceof AssignmentExprent) {
      AssignmentExprent asf = (AssignmentExprent) first;
      AssignmentExprent ass = (AssignmentExprent) second;

      if (isStackVar(asf.getLeft()) && !isStackVar(ass.getLeft()) && asf.getLeft().equals(ass.getRight())) {
        asf.setRight(new AssignmentExprent(ass.getLeft(), asf.getRight(), ass.bytecode));
        return true;
      }
    }

    return false;
  }

  private static boolean isStackVar(Exprent exprent) {
    return exprent instanceof VarExprent && ((VarExprent) exprent).isStack();
  }

  /*
   * If the assignment is of the form:
   * var10001 = xxx;
   * c = xxx // where c IS NOT a stack variable (e.g. a local variable, or array element)
   * and c does not contain var10001, then var10001 is replaced by c, and the calling function
   * will remove the second assignment, essentially removing the first one.
   *
   * This is also applied to the case where the assignment is of the form:
   * a = var10001 = xxx;
   * c = xxx
   * into
   * a = c = xxx;
   * or
   * a = b = var10001 = xxx;
   * c = xxx
   * into
   * a = b = c = xxx;
   * This is also why it replaces the first assignment, and deleting the second, instead of
   * just deleting the second.
   */
  /**
   * RTF: chain two consecutive assignments with the same RHS into a = b = value.
   * javac compiles chained assignments with dup, matching original bytecode that
   * uses dup to assign one value to two local variables.
   *
   * Strict requirements to avoid incorrect chaining:
   * - Both LHS must be local variables (not fields, arrays, or complex expressions)
   * - RHS must be a simple load (variable, field, or constant)
   * - Neither LHS can be the same variable as the RHS (would be sequential, not parallel)
   * - The RHS variable must not appear in either LHS
   */
  private static boolean isChainableAssignment(Exprent first, Exprent second) {
    if (!(first instanceof AssignmentExprent asf) || !(second instanceof AssignmentExprent ass)) {
      return false;
    }
    // Both LHS must be simple local variables
    if (!(asf.getLeft() instanceof VarExprent varA) || !(ass.getLeft() instanceof VarExprent varB)) {
      return false;
    }
    // Same RHS expression
    if (!asf.getRight().equals(ass.getRight())) {
      return false;
    }
    // Don't chain if either side is already a chained assignment
    if (asf.getRight() instanceof AssignmentExprent || ass.getRight() instanceof AssignmentExprent) {
      return false;
    }
    // RHS must be a parameter/argument variable load or a field load on a
    // different object than either LHS. Constants are also safe.
    Exprent rhs = asf.getRight();
    if (rhs instanceof ConstExprent) {
      // Constants are always safe to chain
    } else if (rhs instanceof VarExprent rhsVar) {
      // Must not be either LHS variable
      if (rhsVar.getIndex() == varA.getIndex() || rhsVar.getIndex() == varB.getIndex()) {
        return false;
      }
    } else if (rhs instanceof FieldExprent fieldRhs) {
      // Field load is safe if neither LHS appears in the field's instance
      if (fieldRhs.getInstance() != null && fieldRhs.getInstance().containsExprent(asf.getLeft())) {
        return false;
      }
    } else {
      // No other RHS types - too risky
      return false;
    }
    // LHS variables must be different
    if (varA.getIndex() == varB.getIndex()) {
      return false;
    }
    // Neither LHS variable index can appear anywhere in the other assignment
    if (exprContainsVarIndex(ass.getRight(), varA.getIndex()) || exprContainsVarIndex(asf.getRight(), varB.getIndex())) {
      return false;
    }
    // Chain: first becomes a = (b = value)
    asf.setRight(ass);
    return true;
  }

  /** Check if an expression tree contains any VarExprent with the given index. */
  private static boolean exprContainsVarIndex(Exprent expr, int varIndex) {
    if (expr instanceof VarExprent ve && ve.getIndex() == varIndex) return true;
    for (Exprent sub : expr.getAllExprents(true)) {
      if (sub instanceof VarExprent ve && ve.getIndex() == varIndex) return true;
    }
    return false;
  }

  private static boolean isStackAssignment(Exprent first, Exprent second) {
    if (first instanceof AssignmentExprent && second instanceof AssignmentExprent) {
      AssignmentExprent asf = (AssignmentExprent) first;
      AssignmentExprent ass = (AssignmentExprent) second;

      while (true) {
        if (asf.getRight().equals(ass.getRight())) {
          if (isStackVar (asf.getLeft()) && !isStackVar(ass.getLeft())) {
            if (!ass.getLeft().containsExprent(asf.getLeft())) {
              asf.setRight(ass);
              return true;
            }
          }
        }
        if (asf.getRight() instanceof AssignmentExprent) {
          asf = (AssignmentExprent) asf.getRight();
        } else {
          break;
        }
      }
    }

    return false;
  }

  /*
   * Looking for the following pattern:
   * xxx = xxx + 1; // or xxx - 1, or 1 + xxx (in which case the arguments are swapped)
   * where xxx is not a var exprent
   */
  private static Exprent isPPIorMMI(Exprent first) {
    if (first instanceof AssignmentExprent) {
      AssignmentExprent as = (AssignmentExprent) first;

      if (as.getRight() instanceof FunctionExprent) {
        FunctionExprent func = (FunctionExprent) as.getRight();

        if (func.getFuncType() == FunctionType.ADD || func.getFuncType() == FunctionType.SUB) {
          Exprent econd = func.getLstOperands().get(0);
          Exprent econst = func.getLstOperands().get(1);

          if (!(econst instanceof ConstExprent) && econd instanceof ConstExprent &&
              func.getFuncType() == FunctionType.ADD) {
            econd = econst;
            econst = func.getLstOperands().get(0);
          }

          if (econst instanceof ConstExprent && ((ConstExprent) econst).hasValueOne()) {
            Exprent left = as.getLeft();

            if (!(left instanceof VarExprent) && left.equals(econd)) {
              FunctionType type = func.getFuncType() == FunctionType.ADD ? FunctionType.PPI : FunctionType.MMI;
              FunctionExprent ret = new FunctionExprent(type, econd, func.bytecode);
              ret.setImplicitType(econd.getExprType());
              return ret;
            }
          }
        }
      }
    }

    return null;
  }

  /*
   * Looking for the following pattern:
   * xxx = yyy
   * ++yyy; // or --yyy;
   * and turn it into:
   * xxx = yyy++; // or xxx = yyy--;
   */
  private static boolean isIPPorIMM(Exprent first, Exprent second) {
    if (first instanceof AssignmentExprent && second instanceof FunctionExprent) {
      AssignmentExprent as = (AssignmentExprent) first;
      FunctionExprent in = (FunctionExprent) second;

      if ((in.getFuncType() == FunctionType.MMI || in.getFuncType() == FunctionType.PPI) &&
          in.getLstOperands().get(0).equals(as.getRight())) {

        if (in.getFuncType() == FunctionType.MMI) {
          in.setFuncType(FunctionType.IMM);
        } else {
          in.setFuncType(FunctionType.IPP);
        }
        as.setRight(in);

        return true;
      }
    }

    return false;
  }

  /*
   * Looking for the following pattern:
   * xxx = yyy
   * yyy = xxx + 1; // or a - 1 or 1 + a
   * and xxx is used elsewhere
   * then turn it into:
   * xxx = yyy++;
   */
  private static boolean isIPPorIMM2(Exprent first, Exprent second) {
    if (!(first instanceof AssignmentExprent && second instanceof AssignmentExprent)) {
      return false;
    }

    AssignmentExprent af = (AssignmentExprent) first;
    AssignmentExprent as = (AssignmentExprent) second;

    if (!(as.getRight() instanceof FunctionExprent)) {
      return false;
    }

    FunctionExprent func = (FunctionExprent) as.getRight();

    if (func.getFuncType() != FunctionType.ADD && func.getFuncType() != FunctionType.SUB) {
      return false;
    }

    Exprent econd = func.getLstOperands().get(0);
    Exprent econst = func.getLstOperands().get(1);

    if (!(econst instanceof ConstExprent) && econd instanceof ConstExprent && func.getFuncType() == FunctionType.ADD) {
      econd = econst;
      econst = func.getLstOperands().get(0);
    }

    if (econst instanceof ConstExprent &&
        ((ConstExprent) econst).hasValueOne() &&
        af.getLeft().equals(econd) &&
        af.getRight().equals(as.getLeft()) &&
        (af.getLeft().getExprentUse() & Exprent.MULTIPLE_USES) != 0) {
      FunctionType type = func.getFuncType() == FunctionType.ADD ? FunctionType.IPP : FunctionType.IMM;

      FunctionExprent ret = new FunctionExprent(type, af.getRight(), func.bytecode);
      ret.setImplicitType(VarType.VARTYPE_INT);

      af.setRight(ret);
      return true;
    }

    return false;
  }

  /**
   * Checks whether the isIPPorIMM / isIPPorIMM2 pattern is safe to apply in RTF mode.
   * Safe when: the copy variable is a stack var and is used only as an array index
   * in the expression that follows the two-statement increment pattern.
   *
   * Matches two shapes (both after PPandMMHelper may or may not have run):
   *   copy = idx; ++idx;          arr[copy] = val   (isIPPorIMM pattern)
   *   copy = idx; idx = copy + 1; arr[copy] = val   (isIPPorIMM2 pattern)
   *
   * Stack vars are never merged with real vars, so the FIXME bug in VarVersionsProcessor
   * (where variable merging after inlining corrupts values) cannot occur.
   */
  private static boolean isRTFSafePostIncrement(Exprent first, Exprent second, List<Exprent> list, int index) {
    if (!(first instanceof AssignmentExprent af)) {
      return false;
    }

    // The copy variable must be a stack variable (safe from var merge bugs)
    // or the incremented source must be a field (field access doesn't go
    // through var versioning, so no merge risk).
    if (!(af.getLeft() instanceof VarExprent copyVar)) {
      return false;
    }
    if (!copyVar.isStack() && !(af.getRight() instanceof FieldExprent)) {
      return false;
    }

    // Verify that the second statement is part of the increment pattern:
    // either a PPI/MMI FunctionExprent (isIPPorIMM) or an AssignmentExprent (isIPPorIMM2)
    boolean isIPPorIMMPattern = second instanceof FunctionExprent fn
        && (fn.getFuncType() == FunctionType.MMI || fn.getFuncType() == FunctionType.PPI)
        && fn.getLstOperands().get(0).equals(af.getRight());

    boolean isIPPorIMM2Pattern = second instanceof AssignmentExprent as2
        && as2.getRight() instanceof FunctionExprent fn2
        && (fn2.getFuncType() == FunctionType.ADD || fn2.getFuncType() == FunctionType.SUB)
        && af.getRight().equals(as2.getLeft());

    if (!isIPPorIMMPattern && !isIPPorIMM2Pattern) {
      return false;
    }

    // There must be a following expression that uses the copy var.
    // If there's no third expression in the list, the copy var might be used
    // in a sibling statement (e.g., if-condition). Allow the folding when
    // the source is a field - PPandMMHelper.inlinePPIandMMIIf will handle
    // inlining the post-increment into the if-condition later.
    if (index + 2 >= list.size()) {
      return af.getRight() instanceof FieldExprent;
    }

    Exprent following = list.get(index + 2);
    // Safe if the copy var is used only as an array index
    if (isVarUsedOnlyAsArrayIndex(copyVar, following)) {
      return true;
    }
    // Also safe if the copy var is used only as the right-hand side of a field assignment.
    // Pattern: copy = this.field; this.field++; target.field = copy;
    // This reconstructs to: target.field = this.field++;
    if (following instanceof AssignmentExprent followAssign
        && followAssign.getLeft() instanceof FieldExprent
        && followAssign.getRight() instanceof VarExprent followVar
        && followVar.getIndex() == copyVar.getIndex()
        && followVar.getVersion() == copyVar.getVersion()) {
      return true;
    }
    // Also safe if the copy var is used as the right-hand side of a local variable assignment.
    // Pattern: copy = this.field; this.field++; localVar = copy;
    // This reconstructs to: copy = this.field++; localVar = copy;
    // (and later passes may further inline copy into localVar)
    if (following instanceof AssignmentExprent followAssign
        && followAssign.getLeft() instanceof VarExprent
        && followAssign.getRight() instanceof VarExprent followVar
        && followVar.getIndex() == copyVar.getIndex()
        && followVar.getVersion() == copyVar.getVersion()) {
      return true;
    }
    // Also safe if the copy var is used as a method argument in the following expression.
    // Pattern: copy = this.field; this.field++; x = this.method(copy);
    // This reconstructs to: x = this.method(this.field++);
    if (isVarUsedOnlyAsMethodArg(copyVar, following)) {
      return true;
    }
    // Also safe if the copy var is used in a return statement.
    // Pattern: copy = this.field; this.field++; return (cast)copy;
    // This reconstructs to: return (cast)(this.field++);
    if (following instanceof ExitExprent exit
        && exit.getExitType() == ExitExprent.Type.RETURN
        && exit.getValue() != null) {
      Exprent retVal = exit.getValue();
      // Direct use: return copy
      if (retVal instanceof VarExprent ve
          && ve.getIndex() == copyVar.getIndex()
          && ve.getVersion() == copyVar.getVersion()) {
        return true;
      }
      // Through a cast: return (float)copy, return (short)copy, etc.
      // Handles CAST, I2F, I2D, I2L, I2B, I2S, I2C and other single-operand cast-like functions
      if (retVal instanceof FunctionExprent fn
          && fn.getFuncType().castType != null
          && fn.getLstOperands().size() == 1
          && fn.getLstOperands().get(0) instanceof VarExprent ve
          && ve.getIndex() == copyVar.getIndex()
          && ve.getVersion() == copyVar.getVersion()) {
        return true;
      }
    }
    return false;
  }

  /**
   * Checks if two expressions refer to the same field, comparing by name and classname
   * rather than using FieldExprent.equals() which can fail when the 'this' instance
   * VarExprents have different inferred types.
   */
  private static boolean sameField(Exprent a, Exprent b) {
    if (a instanceof FieldExprent fa && b instanceof FieldExprent fb) {
      return fa.getName().equals(fb.getName())
          && fa.getClassname().equals(fb.getClassname())
          && fa.isStatic() == fb.isStatic();
    }
    return false;
  }

  /**
   * RTF: Folds array element self-increment followed by usage of that element.
   * Pattern:
   *   arr[idx] = arr[idx] + 1;  (self-increment of array element)
   *   target[arr[idx]] = val;   (next statement reads the incremented value)
   * becomes:
   *   target[arr[idx]++] = val; (post-increment returns pre-increment value)
   *
   * This fixes a semantic bug: the original bytecode uses dup2/dup_x2 to capture
   * the pre-increment value for use as an array index, but the split decompilation
   * reads the post-increment value, producing incorrect behavior.
   */
  private static boolean foldArrayElementSelfIncrement(Exprent current, Exprent next) {
    if (!DecompilerContext.isRoundtripFidelity()) return false;

    // current must be: arr[idx] = arr[idx] + 1 (or - 1)
    if (!(current instanceof AssignmentExprent assign)) return false;
    if (!(assign.getLeft() instanceof ArrayExprent incArray)) return false;
    if (!(assign.getRight() instanceof FunctionExprent func)) return false;
    if (func.getFuncType() != FunctionType.ADD && func.getFuncType() != FunctionType.SUB) return false;

    Exprent econd = func.getLstOperands().get(0);
    Exprent econst = func.getLstOperands().get(1);
    if (!(econst instanceof ConstExprent) && econd instanceof ConstExprent && func.getFuncType() == FunctionType.ADD) {
      econd = econst;
      econst = func.getLstOperands().get(0);
    }
    if (!(econst instanceof ConstExprent) || !((ConstExprent) econst).hasValueOne()) return false;
    // Self-increment: left side array element equals the addend
    if (!incArray.equals(econd)) return false;

    // Find the matching array element read in 'next' used as an array index
    Pair<Exprent, ArrayExprent> found = findArrayExprAsIndex(incArray, next);
    if (found == null) return false;

    // Create post-increment: arr[idx]++ (IPP returns old value, then increments)
    FunctionType type = func.getFuncType() == FunctionType.ADD ? FunctionType.IPP : FunctionType.IMM;
    FunctionExprent postInc = new FunctionExprent(type, found.b, func.bytecode);
    postInc.setImplicitType(VarType.VARTYPE_INT);

    // Replace the found array read with the post-increment in the parent
    found.a.replaceExprent(found.b, postInc);
    return true;
  }

  /**
   * Finds an ArrayExprent in the expression tree that equals 'target' and is used
   * as the index of another ArrayExprent. Returns (parent, found) for replacement,
   * or null if not found.
   */
  private static Pair<Exprent, ArrayExprent> findArrayExprAsIndex(ArrayExprent target, Exprent expr) {
    return findArrayExprAsIndexRec(target, expr, null);
  }

  private static Pair<Exprent, ArrayExprent> findArrayExprAsIndexRec(ArrayExprent target, Exprent expr, Exprent parent) {
    if (expr instanceof ArrayExprent arrExpr) {
      // Check if this array's index equals our target
      if (arrExpr.getIndex() instanceof ArrayExprent indexArr && indexArr.equals(target)) {
        return Pair.of((Exprent) arrExpr, indexArr);
      }
      // Recurse into array part
      Pair<Exprent, ArrayExprent> result = findArrayExprAsIndexRec(target, arrExpr.getArray(), arrExpr);
      if (result != null) return result;
      // Recurse into index part
      return findArrayExprAsIndexRec(target, arrExpr.getIndex(), arrExpr);
    }
    // For all other expression types, recurse into sub-expressions
    for (Exprent sub : expr.getAllExprents()) {
      Pair<Exprent, ArrayExprent> result = findArrayExprAsIndexRec(target, sub, expr);
      if (result != null) return result;
    }
    return null;
  }

  /**
   * RTF: folds 3-statement pattern into a single return:
   *   copy = field; field = field + 1; return (cast)copy
   * becomes:
   *   return (cast)(field++)
   *
   * This handles the self-increment case (field = field + 1) that isIPPorIMM2 misses
   * because it expects (field = copy + 1).
   */
  private static boolean foldFieldPostIncrementReturn(List<Exprent> list, int index) {
    if (!DecompilerContext.isRoundtripFidelity()) return false;

    Exprent first = list.get(index);
    Exprent second = list.get(index + 1);
    Exprent third = list.get(index + 2);

    // First: copy = field
    if (!(first instanceof AssignmentExprent af) || !(af.getLeft() instanceof VarExprent copyVar)) return false;
    if (!(af.getRight() instanceof FieldExprent field)) return false;

    // Second: field = field + 1 (assignment form) or field++ (PPI form)
    // Use name-based field comparison because FieldExprent.equals() can fail when
    // the 'this' instance VarExprents have different inferred types across occurrences.
    FunctionType incType;
    BitSet incBytecode;
    if (second instanceof AssignmentExprent as && sameField(field, as.getLeft())
        && as.getRight() instanceof FunctionExprent func
        && (func.getFuncType() == FunctionType.ADD || func.getFuncType() == FunctionType.SUB)) {
      Exprent addend = func.getLstOperands().get(0);
      Exprent constVal = func.getLstOperands().get(1);
      if (!(constVal instanceof ConstExprent) && addend instanceof ConstExprent && func.getFuncType() == FunctionType.ADD) {
        addend = constVal;
        constVal = func.getLstOperands().get(0);
      }
      if (!(constVal instanceof ConstExprent) || !((ConstExprent) constVal).hasValueOne()) return false;
      if (!sameField(field, addend)) return false;
      incType = func.getFuncType() == FunctionType.ADD ? FunctionType.IPP : FunctionType.IMM;
      incBytecode = func.bytecode;
    } else if (second instanceof FunctionExprent ppi
        && (ppi.getFuncType() == FunctionType.PPI || ppi.getFuncType() == FunctionType.MMI)
        && sameField(field, ppi.getLstOperands().get(0))) {
      incType = ppi.getFuncType() == FunctionType.PPI ? FunctionType.IPP : FunctionType.IMM;
      incBytecode = ppi.bytecode;
    } else {
      return false;
    }

    // Third: return (cast)copy or return copy
    if (!(third instanceof ExitExprent exit) || exit.getExitType() != ExitExprent.Type.RETURN || exit.getValue() == null) return false;

    VarExprent retVar = null;
    Exprent retVal = exit.getValue();
    if (retVal instanceof VarExprent ve) {
      retVar = ve;
    } else if (retVal instanceof FunctionExprent fn && fn.getFuncType().castType != null
        && fn.getLstOperands().size() == 1 && fn.getLstOperands().get(0) instanceof VarExprent ve) {
      retVar = ve;
    }
    if (retVar == null || retVar.getIndex() != copyVar.getIndex() || retVar.getVersion() != copyVar.getVersion()) return false;

    // All checks pass. Fold: create field++ and replace copy in return.
    FunctionType type = incType;
    FunctionExprent postInc = new FunctionExprent(type, field, incBytecode);
    postInc.setImplicitType(VarType.VARTYPE_INT);

    // Replace the copy var in the return with the post-increment expression
    if (retVal instanceof VarExprent) {
      exit.replaceExprent(retVal, postInc);
    } else if (retVal instanceof FunctionExprent fn) {
      fn.getLstOperands().set(0, postInc);
    }

    // Remove first two statements (copy assignment and increment)
    list.remove(index + 1); // remove increment
    list.remove(index);     // remove copy assignment
    return true;
  }

  /**
   * Checks that a variable appears in the expression tree ONLY as a parameter of an InvocationExprent.
   */
  private static boolean isVarUsedOnlyAsMethodArg(VarExprent var, Exprent expr) {
    // The expression should be an assignment whose RHS contains a method call with the var as arg
    Exprent toCheck = expr;
    if (expr instanceof AssignmentExprent ae) {
      // The var must not be on the LHS
      if (ae.getLeft() instanceof VarExprent ve
          && ve.getIndex() == var.getIndex() && ve.getVersion() == var.getVersion()) {
        return false;
      }
      toCheck = ae.getRight();
    }
    // Walk the expression tree to find the var
    boolean[] found = {false};
    if (!checkVarAsMethodArgOnly(var, toCheck, null, found)) {
      return false;
    }
    return found[0];
  }

  private static boolean checkVarAsMethodArgOnly(VarExprent var, Exprent expr, Exprent parent, boolean[] found) {
    if (expr instanceof VarExprent ve) {
      if (ve.getIndex() == var.getIndex() && ve.getVersion() == var.getVersion()) {
        // Check that parent is an InvocationExprent and this var is a parameter
        if (parent instanceof InvocationExprent inv) {
          if (inv.getLstParameters().contains(expr)) {
            found[0] = true;
            return true;
          }
        }
        return false; // var used in non-method-arg position
      }
      return true;
    }
    for (Exprent sub : expr.getAllExprents()) {
      if (!checkVarAsMethodArgOnly(var, sub, expr, found)) {
        return false;
      }
    }
    return true;
  }

  /**
   * Checks that a variable appears in the expression tree ONLY as the index of an ArrayExprent,
   * and appears at least once.
   */
  private static boolean isVarUsedOnlyAsArrayIndex(VarExprent var, Exprent expr) {
    boolean[] found = {false};
    if (!checkVarAsArrayIndexOnly(var, expr, null, found)) {
      return false;
    }
    return found[0];
  }

  /**
   * Recursively checks that every occurrence of var in the expression tree is used
   * as the index of an ArrayExprent. Returns false if the var appears in a non-index position.
   */
  private static boolean checkVarAsArrayIndexOnly(VarExprent var, Exprent expr, Exprent parent, boolean[] found) {
    if (expr instanceof VarExprent ve) {
      if (ve.getIndex() == var.getIndex() && ve.getVersion() == var.getVersion()) {
        // This var matches - check that its parent is an ArrayExprent and this var is the index
        if (parent instanceof ArrayExprent arrParent && arrParent.getIndex() == expr) {
          found[0] = true;
          return true;
        }
        // Var used in a non-array-index position
        return false;
      }
      return true;
    }

    if (expr instanceof ArrayExprent arrExpr) {
      // Check the array sub-expression normally (var must not appear there)
      if (!checkVarAsArrayIndexOnly(var, arrExpr.getArray(), arrExpr, found)) {
        return false;
      }
      // Check the index sub-expression with this ArrayExprent as parent
      return checkVarAsArrayIndexOnly(var, arrExpr.getIndex(), arrExpr, found);
    }

    // For all other expression types, recurse into sub-expressions
    for (Exprent sub : expr.getAllExprents()) {
      if (!checkVarAsArrayIndexOnly(var, sub, expr, found)) {
        return false;
      }
    }
    return true;
  }

  // Inlines PPI into the next expression, to make stack var simplificiation easier
  //
  // ++i;
  // array[i] = 2;
  //
  // turns into
  //
  // array[++i] = 2;
  //
  // While this helps simplify stack vars, it also has can potentially make invalid code! When evaluating ppmm correctness, this is a good place to start.
  // TODO: fernflower preference?
  private static boolean inlinePPIAndMMI(Exprent expr, Exprent next) {
    if (expr instanceof FunctionExprent) {
      FunctionExprent func = (FunctionExprent) expr;

      if (func.getFuncType() == FunctionType.PPI || func.getFuncType() == FunctionType.MMI) {
        if (func.getLstOperands().get(0) instanceof VarExprent) {
          VarExprent var = (VarExprent) func.getLstOperands().get(0);

          // Can't inline ppmm into next ppmm
          if (next instanceof FunctionExprent) {
            if (isPPMM((FunctionExprent) next)) {
              return false;
            }
          }

          // Try to find the next use of the variable
          Pair<Exprent, VarExprent> usage = findFirstValidUsage(var, next);

          // Found usage
          if (usage != null) {
            // Replace exprent
            usage.a.replaceExprent(usage.b, func);
            return true;
          }
        }
      }
    }

    return false;
  }

  // Try to find the first valid usage of a variable for PPMM inlining.
  // Returns Pair{parent exprent, variable exprent to replace}
  private static Pair<Exprent, VarExprent> findFirstValidUsage(VarExprent match, Exprent next) {
    List<Exprent> stack = new ArrayList<>();
    List<Exprent> parent = new ArrayList<>();
    stack.add(next);
    parent.add(null);

    while (!stack.isEmpty()) {
      Exprent expr = stack.remove(stack.size() - 1);
      Exprent parentExpr = parent.remove(parent.size() - 1);

      List<Exprent> exprents = expr.getAllExprents();

      if (parentExpr != null &&
        expr instanceof VarExprent ve &&
        ve.getIndex() == match.getIndex() &&
        ve.getVersion() == match.getVersion()) {
        return Pair.of(parentExpr, ve);
      }

      if (expr instanceof FunctionExprent) {
        FunctionExprent func = (FunctionExprent) expr;

        // Don't inline ppmm into more ppmm
        if (isPPMM(func)) {
          return null;
        }

        // Don't consider || or &&
        if (func.getFuncType() == FunctionType.BOOLEAN_OR || func.getFuncType() == FunctionType.BOOLEAN_AND) {
          return null;
        }

        // Don't consider ternaries
        if (func.getFuncType() == FunctionType.TERNARY) {
          return null;
        }

        // Subtraction and division make it hard to deduce which variable is used, especially without SSAU, so cancel if we find
        if (func.getFuncType() == FunctionType.SUB || func.getFuncType() == FunctionType.DIV) {
          return null;
        }
      }

      // Reverse iteration to ensure DFS
      for (int i = exprents.size() - 1; i >= 0; i--) {
        Exprent ex = exprents.get(i);

        // Avoid making something like `++a = 5`. It shouldn't happen but better be safe than sorry.
        if (expr instanceof AssignmentExprent asExpr &&
          ex == asExpr.getLeft() &&
          ex instanceof VarExprent innerEx &&
          innerEx.getIndex() == match.getIndex()
        ) {
          continue;
        }

        stack.add(ex);
        parent.add(expr);
      }
    }

    // Couldn't find
    return null;
  }

  private static boolean isPPMM(FunctionExprent func) {
    return
      func.getFuncType() == FunctionType.PPI ||
      func.getFuncType() == FunctionType.MMI ||
      func.getFuncType() == FunctionType.IPP ||
      func.getFuncType() == FunctionType.IMM;
  }

  private static boolean isMonitorExit(Exprent first) {
    if (first instanceof MonitorExprent) {
      MonitorExprent expr = (MonitorExprent) first;
      return expr.getMonType() == MonitorExprent.Type.EXIT &&
             expr.getValue() instanceof VarExprent &&
             !((VarExprent) expr.getValue()).isStack() &&
             expr.isRemovable();
    }

    return false;
  }

  private static boolean hasQualifiedNewGetClass(Statement parent, Statement child) {
    if (child instanceof BasicBlockStatement && child.getExprents() != null && !child.getExprents().isEmpty()) {
      Exprent firstExpr = child.getExprents().get(child.getExprents().size() - 1);

      if (parent instanceof IfStatement) {
        if (isQualifiedNewGetClass(firstExpr, ((IfStatement) parent).getHeadexprent().getCondition())) {
          child.getExprents().remove(firstExpr);
          return true;
        }
      }
      // TODO DoStatements ?
    }
    return false;
  }

  private static boolean isQualifiedNewGetClass(Exprent first, Exprent second) {
    if (first instanceof InvocationExprent) {
      InvocationExprent invocation = (InvocationExprent) first;

      if ((!invocation.isStatic() &&
           invocation.getName().equals("getClass") && invocation.getStringDescriptor().equals("()Ljava/lang/Class;")) // J8
          || (invocation.isStatic() && invocation.getClassname().equals("java/util/Objects") && invocation.getName().equals("requireNonNull")
              && invocation.getStringDescriptor().equals("(Ljava/lang/Object;)Ljava/lang/Object;"))) { // J9+

        // Don't strip based on syntheticNullCheck flag alone — the heuristic
        // (next opcode is a constant load) catches standalone null checks like
        // Objects.requireNonNull(param) before a loop counter init (iconst_0)
        // or a float literal (ldc). Fall through to verify there's actually an
        // inner class creation in the next expression.

        Deque<Exprent> lstExprents = new ArrayDeque<>();
        lstExprents.add(second);

        final Exprent target;
        if (invocation.isStatic()) { // Objects.requireNonNull(target) (J9+)
          // detect target type
          target = invocation.getLstParameters().get(0);
        } else { // target.getClass() (J8)
          target = invocation.getInstance();
        }

        while (!lstExprents.isEmpty()) {
          Exprent expr = lstExprents.removeFirst();
          lstExprents.addAll(expr.getAllExprents());
          if (expr instanceof NewExprent) {
            NewExprent newExpr = (NewExprent) expr;
            if (newExpr.getConstructor() != null && !newExpr.getConstructor().getLstParameters().isEmpty() &&
                (newExpr.getConstructor().getLstParameters().get(0).equals(target) ||
                 isUnambiguouslySameParam(invocation.isStatic(), target, newExpr.getConstructor().getLstParameters()))) {

              String classname = newExpr.getNewType().value;
              ClassNode node = DecompilerContext.getClassProcessor().getMapRootClasses().get(classname);
              if (node != null && node.type != ClassNode.Type.ROOT) {
                return true;
              }
            }
          }
        }
      }
    }

    return false;
  }

  private static boolean isUnambiguouslySameParam(boolean isStatic, Exprent target, List<Exprent> parameters) {
    boolean firstParamOfSameType = parameters.get(0).getExprType().equals(target.getExprType());
    if (!isStatic) { // X.getClass()/J8, this is less likely to overlap with legitimate use
      return firstParamOfSameType;
    }
    // Calling Objects.requireNonNull and discarding the result is a common pattern in normal code, so we have to be a bit more
    // cautious about stripping calls when a constructor takes parameters of the instance type
    // ex. given a class X, `Objects.requireNonNull(someInstanceOfX); new X(someInstanceOfX)` should not have the rNN stripped.
    if (!firstParamOfSameType) {
      return false;
    }

    for (int i = 1; i < parameters.size(); i++) {
      if (parameters.get(i).getExprType().equals(target.getExprType())) {
        return false;
      }
    }

    return true;
  }

  // var10000 = get()
  // var10000[0] = var10000[0] + 10;
  //
  // becomes
  //
  // get()[0] = get()[0] + 10;
  //
  // which then becomes
  //
  // get()[0] += 10;
  //
  // when assignments are updated at the very end of the processing pipeline. This method assumes assignment updating will always happen, otherwise it'll lead to duplicated code execution!
  // FIXME: Move to a more reasonable place or implement assignment merging in StackVarsProcessor!
  private static boolean isMethodArrayAssign(Exprent expr, Exprent next) {
    if (expr instanceof AssignmentExprent && next instanceof AssignmentExprent) {
      Exprent firstLeft = ((AssignmentExprent) expr).getLeft();
      Exprent secondLeft = ((AssignmentExprent) next).getLeft();


      if (firstLeft instanceof VarExprent && secondLeft instanceof ArrayExprent) {
        Exprent secondBase = ((ArrayExprent) secondLeft).getArray();

        if (secondBase instanceof VarExprent && ((VarExprent) firstLeft).getIndex() == ((VarExprent) secondBase).getIndex() && ((VarExprent) secondBase).isStack()) {

          boolean foundAssign = false;
          Exprent secondRight = ((AssignmentExprent) next).getRight();
          for (Exprent exprent : secondRight.getAllExprents()) {
            if (exprent instanceof ArrayExprent &&
                ((ArrayExprent) exprent).getArray() instanceof VarExprent &&
                ((VarExprent) ((ArrayExprent) exprent).getArray()).getIndex() == ((VarExprent) firstLeft).getIndex()) {
              exprent.replaceExprent(((ArrayExprent) exprent).getArray(), ((AssignmentExprent) expr).getRight().copy());
              foundAssign = true;
            }
          }

          if (foundAssign) {
            secondLeft.replaceExprent(secondBase, ((AssignmentExprent) expr).getRight());
            return true;
          }
        }
      }
    }

    return false;
  }

  // propagate (var = new X) forward to the <init> invocation
  private static boolean isConstructorInvocationRemote(List<Exprent> list, int index) {
    Exprent current = list.get(index);

    if (current instanceof AssignmentExprent) {
      AssignmentExprent as = (AssignmentExprent) current;

      if (as.getLeft() instanceof VarExprent && as.getRight() instanceof NewExprent) {

        NewExprent newExpr = (NewExprent) as.getRight();
        VarType newType = newExpr.getNewType();
        VarVersionPair leftPair = new VarVersionPair((VarExprent) as.getLeft());

        if (newType.type == CodeType.OBJECT && newType.arrayDim == 0 && newExpr.getConstructor() == null) {
          for (int i = index + 1; i < list.size(); i++) {
            Exprent remote = list.get(i);

            // <init> invocation
            if (remote instanceof InvocationExprent) {
              InvocationExprent in = (InvocationExprent) remote;

              if (in.getFunctype() == InvocationExprent.Type.INIT &&
                  in.getInstance() instanceof VarExprent &&
                  as.getLeft().equals(in.getInstance())) {
                newExpr.setConstructor(in);
                in.setInstance(null);

                list.set(i, as.copy());

                return true;
              }
            }

            // check for variable in use
            Set<VarVersionPair> setVars = remote.getAllVariables();
            if (setVars.contains(leftPair)) { // variable used somewhere in between -> exit, need a better reduced code
              return false;
            }
          }
        }
      }
    }

    return false;
  }

  // Some constructor invocations use swap to call <init>.
  //
  // Type type = new Type;
  // var = type;
  // type.<init>(...);
  //
  // turns into
  //
  // var = new Type(...);
  //
  private static boolean isSwapConstructorInvocation(Exprent last, Exprent expr, Exprent next) {
    if (last instanceof AssignmentExprent && expr instanceof AssignmentExprent && next instanceof InvocationExprent) {
      AssignmentExprent asLast = (AssignmentExprent) last;
      AssignmentExprent asExpr = (AssignmentExprent) expr;
      InvocationExprent inNext = (InvocationExprent) next;

      // Make sure the next invocation is a constructor invocation!
      if (inNext.getFunctype() != InvocationExprent.Type.INIT) {
        return false;
      }

      if (asLast.getLeft() instanceof VarExprent && asExpr.getRight() instanceof VarExprent && inNext.getInstance() != null && inNext.getInstance() instanceof VarExprent) {
        VarExprent varLast = (VarExprent) asLast.getLeft();
        VarExprent varExpr = (VarExprent) asExpr.getRight();
        VarExprent varNext = (VarExprent) inNext.getInstance();

        if (varLast.getIndex() == varExpr.getIndex() && varExpr.getIndex() == varNext.getIndex()) {
          if (asLast.getRight() instanceof NewExprent) {
            // Create constructor
            inNext.setInstance(null);
            NewExprent newExpr = (NewExprent) asLast.getRight();
            newExpr.setConstructor(inNext);

            asExpr.setRight(newExpr);

            return true;
          }
        }
      }
    }


    return false;
  }

  private static Exprent isLambda(Exprent exprent, StructClass cl) {
    List<Exprent> lst = exprent.getAllExprents();
    for (Exprent expr : lst) {
      Exprent ret = isLambda(expr, cl);
      if (ret != null) {
        exprent.replaceExprent(expr, ret);
      }
    }

    if (exprent instanceof InvocationExprent) {
      InvocationExprent in = (InvocationExprent) exprent;

      if (in.getInvocationType() == InvocationExprent.InvocationType.DYNAMIC) {
        String lambda_class_name = cl.qualifiedName + in.getInvokeDynamicClassSuffix();
        ClassNode lambda_class = DecompilerContext.getClassProcessor().getMapRootClasses().get(lambda_class_name);

        if (lambda_class != null) { // real lambda class found, replace invocation with an anonymous class
          NewExprent newExpr = new NewExprent(new VarType(lambda_class_name, true), null, 0, in.bytecode);
          newExpr.setConstructor(in);
          // note: we don't set the instance to null with in.setInstance(null) like it is done for a common constructor invocation
          // lambda can also be a reference to a virtual method (e.g. String x; ...(x::toString);)
          // in this case instance will hold the corresponding object

          return newExpr;
        }
      }
    }

    return null;
  }

  private static Exprent isSimpleConstructorInvocation(Exprent exprent) {
    List<Exprent> lst = exprent.getAllExprents();
    for (Exprent expr : lst) {
      Exprent ret = isSimpleConstructorInvocation(expr);
      if (ret != null) {
        exprent.replaceExprent(expr, ret);
      }
    }

    if (exprent instanceof InvocationExprent) {
      InvocationExprent in = (InvocationExprent) exprent;
      if (in.getFunctype() == InvocationExprent.Type.INIT && in.getInstance() instanceof NewExprent) {
        NewExprent newExpr = (NewExprent) in.getInstance();
        newExpr.setConstructor(in);
        in.setInstance(null);
        return newExpr;
      }
    }

    return null;
  }

  private static boolean buildIff(Statement stat, SSAConstructorSparseEx ssa) {
    if (stat instanceof IfStatement && stat.getExprents() == null) {
      // In roundtrip fidelity mode, skip if-else-to-ternary for RETURN statements.
      // "if (cond) return a; else return b;" → "return cond ? a : b;" changes bytecode
      // (two return instructions become one). Assignment ternaries are allowed since
      // they're needed for correct code generation of constructor/new expressions.
      // (Blocking those causes "new ClassName;" without parentheses.)

      IfStatement statement = (IfStatement) stat;
      Exprent ifHeadExpr = statement.getHeadexprent();
      BitSet ifHeadExprBytecode = (ifHeadExpr == null ? null : ifHeadExpr.bytecode);

      if (statement.iftype == IfStatement.IFTYPE_IFELSE) {
        Statement ifStatement = statement.getIfstat();
        Statement elseStatement = statement.getElsestat();

        if (ifStatement.getExprents() != null && ifStatement.getExprents().size() == 1 &&
            elseStatement.getExprents() != null && elseStatement.getExprents().size() == 1 &&
            ifStatement.getAllSuccessorEdges().size() == 1 && elseStatement.getAllSuccessorEdges().size() == 1 &&
            ifStatement.getAllSuccessorEdges().get(0).getDestination() == elseStatement.getAllSuccessorEdges().get(0).getDestination()) {
          Exprent ifExpr = ifStatement.getExprents().get(0);
          Exprent elseExpr = elseStatement.getExprents().get(0);

          if (ifExpr instanceof AssignmentExprent && elseExpr instanceof AssignmentExprent) {
            AssignmentExprent ifAssign = (AssignmentExprent) ifExpr;
            AssignmentExprent elseAssign = (AssignmentExprent) elseExpr;

            if (ifAssign.getLeft() instanceof VarExprent && elseAssign.getLeft() instanceof VarExprent) {
              VarExprent ifVar = (VarExprent) ifAssign.getLeft();
              VarExprent elseVar = (VarExprent) elseAssign.getLeft();

              if (ifVar.getIndex() == elseVar.getIndex() && ifVar.isStack()) {
                boolean found = false;

                // Can happen in EliminateLoopsHelper
                if (ssa == null) {
                  throw new IllegalStateException("Trying to make ternary but have no SSA-Form! How is this possible?");
                }

                for (Entry<VarVersionPair, FastSparseSet<Integer>> ent : ssa.getPhi().entrySet()) {
                  if (ent.getKey().var == ifVar.getIndex()) {
                    if (ent.getValue().contains(ifVar.getVersion()) && ent.getValue().contains(elseVar.getVersion())) {
                      found = true;
                      break;
                    }
                  }
                }

                // RTF: skip ternary folding when the merge-point invokes a method on the
                // stack variable (tail-merge pattern). In the original bytecode each branch
                // has its own copy of the invocation (e.g. .booleanValue()), but a ternary
                // shares it, producing one fewer instruction after recompilation.
                if (found && DecompilerContext.isRoundtripFidelity()) {
                  Statement mergeTarget = ifStatement.getAllSuccessorEdges().get(0).getDestination();
                  if (mergeTarget != null && hasTailMergeUnboxing(mergeTarget, ifVar.getIndex())) {
                    found = false;
                  }
                }

                if (found) {
                  List<Exprent> data = new ArrayList<>(statement.getFirst().getExprents());

                  List<Exprent> operands = Arrays.asList(statement.getHeadexprent().getCondition(), ifAssign.getRight(), elseAssign.getRight());
                  data.add(new AssignmentExprent(ifVar, new FunctionExprent(FunctionType.TERNARY, operands, ifHeadExprBytecode), ifHeadExprBytecode));
                  statement.setExprents(data);

                  if (statement.getAllSuccessorEdges().isEmpty()) {
                    StatEdge ifEdge = ifStatement.getAllSuccessorEdges().get(0);
                    StatEdge edge = new StatEdge(ifEdge.getType(), statement, ifEdge.getDestination());

                    statement.addSuccessor(edge);
                    if (ifEdge.closure != null) {
                      ifEdge.closure.addLabeledEdge(edge);
                    }
                  }

                  SequenceHelper.destroyAndFlattenStatement(statement);

                  return true;
                }
              }
            }
          } else if (ifExpr instanceof ExitExprent && elseExpr instanceof ExitExprent) {
            // RTF: skip return ternary collapse when the original had separate returns
            // (two ireturn instructions). Allow when the original had a shared return
            // (one ireturn fed by both paths) because NOT collapsing creates a temp
            // variable that adds narrowing casts (i2b/i2s) for byte/short methods.
            if (DecompilerContext.isRoundtripFidelity()) {
              // Shared return = both ExitExprents have overlapping bytecode offsets
              boolean sharedReturn = ifExpr.bytecode != null && elseExpr.bytecode != null
                  && ifExpr.bytecode.intersects(elseExpr.bytecode);
              if (!sharedReturn) {
                return false;
              }
            }
            ExitExprent ifExit = (ExitExprent) ifExpr;
            ExitExprent elseExit = (ExitExprent) elseExpr;

            if (ifExit.getExitType() == elseExit.getExitType() && ifExit.getValue() != null && elseExit.getValue() != null &&
                ifExit.getExitType() == ExitExprent.Type.RETURN) {
              // throw is dangerous, because of implicit casting to a common superclass
              // e.g. throws IOException and throw true?new RuntimeException():new IOException(); won't work
              if (ifExit.getExitType() == ExitExprent.Type.THROW &&
                  !ifExit.getValue().getExprType().equals(elseExit.getValue().getExprType())) {  // note: getExprType unreliable at this point!
                return false;
              }

              // avoid flattening to 'iff' if any of the branches is an 'iff' already
              if (isIff(ifExit.getValue()) || isIff(elseExit.getValue())) {
                return false;
              }

              List<Exprent> data = new ArrayList<>(statement.getFirst().getExprents());

              data.add(new ExitExprent(ifExit.getExitType(), new FunctionExprent(FunctionType.TERNARY,
                Arrays.asList(
                  statement.getHeadexprent().getCondition(),
                  ifExit.getValue(),
                  elseExit.getValue()), ifHeadExprBytecode), ifExit.getRetType(), ifHeadExprBytecode, ifExit.getMethodDescriptor()));
              statement.setExprents(data);

              StatEdge retEdge = ifStatement.getAllSuccessorEdges().get(0);
              Statement closure = retEdge.closure == statement ? statement.getParent() : retEdge.closure;
              statement.addSuccessor(new StatEdge(StatEdge.TYPE_BREAK, statement, retEdge.getDestination(), closure));

              SequenceHelper.destroyAndFlattenStatement(statement);

              return true;
            }
          }
        }
      }
    }

    return false;
  }

  private static boolean isIff(Exprent exp) {
    return exp instanceof FunctionExprent && ((FunctionExprent) exp).getFuncType() == FunctionType.TERNARY;
  }

  /**
   * Checks whether the merge-point statement applies an unboxing call on a given
   * stack variable. When both branches of an if-else assign a boxed value to the
   * same stack var and the merge-point then unboxes it (e.g. {@code .booleanValue()}),
   * folding the assignments into a ternary lets javac emit a single shared unboxing
   * call instead of one per branch, changing the instruction count by -1.
   */
  private static boolean hasTailMergeUnboxing(Statement mergeTarget, int stackVarIndex) {
    List<Exprent> exprents = mergeTarget.getExprents();
    if (exprents == null || exprents.isEmpty()) {
      return false;
    }
    for (Exprent expr : exprents) {
      for (Exprent sub : expr.getAllExprents(true, true)) {
        if (sub instanceof InvocationExprent inv && inv.isUnboxingCall()) {
          Exprent instance = inv.getInstance();
          if (instance instanceof VarExprent && ((VarExprent) instance).getIndex() == stackVarIndex) {
            return true;
          }
        }
      }
    }
    return false;
  }

  private static boolean collapseInlinedClass14(Statement stat) {
    boolean ret = class14Builder.match(stat);
    if (ret) {
      String class_name = (String) class14Builder.getVariableValue("$classname$");
      AssignmentExprent assignment = (AssignmentExprent) class14Builder.getVariableValue("$assignfield$");
      FieldExprent fieldExpr = (FieldExprent) class14Builder.getVariableValue("$field$");

      assignment.replaceExprent(assignment.getRight(), new ConstExprent(VarType.VARTYPE_CLASS, class_name, null));

      List<Exprent> data = new ArrayList<>(stat.getFirst().getExprents());

      stat.setExprents(data);

      SequenceHelper.destroyAndFlattenStatement(stat);

      ClassWrapper wrapper = (ClassWrapper) DecompilerContext.getContextProperty(DecompilerContext.CURRENT_CLASS_WRAPPER);
      if (wrapper != null) {
        wrapper.getHiddenMembers().add(InterpreterUtil.makeUniqueKey(fieldExpr.getName(), fieldExpr.getDescriptor().descriptorString));
      }
    }

    return ret;
  }
}
