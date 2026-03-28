// Copyright 2000-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.modules.decompiler;

import org.jetbrains.java.decompiler.code.CodeConstants;
import org.jetbrains.java.decompiler.code.Instruction;
import org.jetbrains.java.decompiler.code.InstructionSequence;
import org.jetbrains.java.decompiler.code.cfg.BasicBlock;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.collectors.ImportCollector;
import org.jetbrains.java.decompiler.modules.decompiler.flow.DirectEdgeType;
import org.jetbrains.java.decompiler.struct.gen.CodeType;
import org.jetbrains.java.decompiler.util.collections.ListStack;
import org.jetbrains.java.decompiler.util.TextBuffer;
import org.jetbrains.java.decompiler.modules.decompiler.exps.*;
import org.jetbrains.java.decompiler.modules.decompiler.exps.FunctionExprent.FunctionType;
import org.jetbrains.java.decompiler.modules.decompiler.flow.DirectGraph;
import org.jetbrains.java.decompiler.modules.decompiler.flow.DirectNode;
import org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper;
import org.jetbrains.java.decompiler.modules.decompiler.stats.*;
import org.jetbrains.java.decompiler.modules.decompiler.vars.VarProcessor;
import org.jetbrains.java.decompiler.main.rels.MethodWrapper;
import org.jetbrains.java.decompiler.struct.StructClass;
import org.jetbrains.java.decompiler.struct.attr.StructBootstrapMethodsAttribute;
import org.jetbrains.java.decompiler.struct.attr.StructGeneralAttribute;
import org.jetbrains.java.decompiler.struct.consts.ConstantPool;
import org.jetbrains.java.decompiler.struct.consts.LinkConstant;
import org.jetbrains.java.decompiler.struct.consts.PooledConstant;
import org.jetbrains.java.decompiler.struct.consts.PrimitiveConstant;
import org.jetbrains.java.decompiler.struct.gen.FieldDescriptor;
import org.jetbrains.java.decompiler.struct.gen.MethodDescriptor;
import org.jetbrains.java.decompiler.struct.gen.TypeFamily;
import org.jetbrains.java.decompiler.struct.gen.VarType;
import org.jetbrains.java.decompiler.struct.gen.generics.GenericType;
import org.jetbrains.java.decompiler.util.TextUtil;

import java.util.*;

public class ExprProcessor implements CodeConstants {
  public static final String UNDEFINED_TYPE_STRING = "<undefinedtype>";
  public static final String UNREPRESENTABLE_TYPE_STRING = "<unrepresentable>";
  public static final String UNKNOWN_TYPE_STRING = "<unknown>";
  public static final String NULL_TYPE_STRING = "<null>";

  private static final Map<Integer, FunctionType> mapConsts = new HashMap<>();
  static {
    mapConsts.put(opc_arraylength, FunctionType.ARRAY_LENGTH);
    mapConsts.put(opc_checkcast, FunctionType.CAST);
    mapConsts.put(opc_instanceof, FunctionType.INSTANCEOF);
  }

  private static final VarType[] consts = {
    VarType.VARTYPE_INT, VarType.VARTYPE_FLOAT, VarType.VARTYPE_LONG, VarType.VARTYPE_DOUBLE, VarType.VARTYPE_CLASS, VarType.VARTYPE_STRING
  };

  private static final VarType[] varTypes = {
    VarType.VARTYPE_INT, VarType.VARTYPE_LONG, VarType.VARTYPE_FLOAT, VarType.VARTYPE_DOUBLE, VarType.VARTYPE_OBJECT
  };

  private static final VarType[] arrTypes = {
    VarType.VARTYPE_INT, VarType.VARTYPE_LONG, VarType.VARTYPE_FLOAT, VarType.VARTYPE_DOUBLE, VarType.VARTYPE_OBJECT,
    VarType.VARTYPE_BOOLEAN, VarType.VARTYPE_CHAR, VarType.VARTYPE_SHORT
  };

  private static final FunctionType[] func1 = {
    FunctionType.ADD, FunctionType.SUB, FunctionType.MUL, FunctionType.DIV,
    FunctionType.REM
  };
  private static final FunctionType[] func2 = {
    FunctionType.SHL, FunctionType.SHR, FunctionType.USHR, FunctionType.AND,
    FunctionType.OR, FunctionType.XOR
  };
  private static final FunctionType[] func3 = {
    FunctionType.I2L, FunctionType.I2F, FunctionType.I2D, FunctionType.L2I,
    FunctionType.L2F, FunctionType.L2D, FunctionType.F2I, FunctionType.F2L,
    FunctionType.F2D, FunctionType.D2I, FunctionType.D2L, FunctionType.D2F,
    FunctionType.I2B, FunctionType.I2C, FunctionType.I2S
  };
  private static final FunctionType[] func4 = {
    FunctionType.LCMP, FunctionType.FCMPL, FunctionType.FCMPG, FunctionType.DCMPL,
    FunctionType.DCMPG
  };
  private static final IfExprent.Type[] func5 = {
    IfExprent.Type.EQ, IfExprent.Type.NE, IfExprent.Type.LT, IfExprent.Type.GE, IfExprent.Type.GT, IfExprent.Type.LE
  };
  private static final IfExprent.Type[] func6 = {
    IfExprent.Type.ICMPEQ, IfExprent.Type.ICMPNE, IfExprent.Type.ICMPLT, IfExprent.Type.ICMPGE, IfExprent.Type.ICMPGT, IfExprent.Type.ICMPLE,
    IfExprent.Type.ACMPEQ, IfExprent.Type.ACMPNE
  };
  private static final IfExprent.Type[] func7 = {IfExprent.Type.NULL, IfExprent.Type.NONNULL};
  private static final MonitorExprent.Type[] func8 = {MonitorExprent.Type.ENTER, MonitorExprent.Type.EXIT};

  private static final CodeType[] arrTypeIds = {
    CodeType.BOOLEAN, CodeType.CHAR, CodeType.FLOAT, CodeType.DOUBLE,
    CodeType.BYTE, CodeType.SHORT, CodeType.INT, CodeType.LONG
  };

  private static final String[] typeNames = {"byte", "char", "double", "float", "int", "long", "short", "boolean"};

  private final MethodDescriptor methodDescriptor;
  private final VarProcessor varProcessor;

  public ExprProcessor(MethodDescriptor md, VarProcessor varProc) {
    methodDescriptor = md;
    varProcessor = varProc;
  }

  public void processStatement(RootStatement root, StructClass cl) {
    FlattenStatementsHelper flatHelper = new FlattenStatementsHelper();
    DirectGraph dgraph = flatHelper.buildDirectGraph(root);

    ValidationHelper.validateDGraph(dgraph, root);

    // TODO: use DirectNode instead DirectNode.id
    Map<String, VarExprent> mapCatch = new HashMap<>();
    collectCatchVars(root, flatHelper, mapCatch);

    Map<DirectNode, PrimitiveExprsList> mapData = new HashMap<>();

    ListStack<DirectNode> stack = new ListStack<>();

    stack.push(dgraph.first);
    mapData.put(dgraph.first, new PrimitiveExprsList());

    while (!stack.isEmpty()) {

      DirectNode node = stack.pop();

      PrimitiveExprsList data;
      if (mapCatch.containsKey(node.id)) {
        data = getExpressionData(mapCatch.get(node.id));
      } else {
        data = mapData.get(node);
      }

      BasicBlockStatement block = node.block;
      if (block != null) {
        processBlock(block, data, cl);
        block.setExprents(data.getLstExprents());
      }

      // TODO: is this copying the stack into catch and finally blocks? It shouldn't do that.
      for (var cd : node.getSuccessors(DirectEdgeType.REGULAR)) {
        DirectNode nd = cd.getDestination();
        if (!mapData.containsKey(nd)) {
          mapData.put(nd, copyVarExprents(data.copyStack()));
          stack.add(nd);
        }
      }
    }

    initStatementExprents(root);
  }

  private static PrimitiveExprsList copyVarExprents(PrimitiveExprsList data) {
    ListStack<Exprent> stack = data.getStack();
    copyEntries(stack);
    return data;
  }

  public static void copyEntries(List<Exprent> stack) {
    for (int i = 0; i < stack.size(); i++) {
      stack.set(i, stack.get(i).copy());
    }
  }

  private static void collectCatchVars(Statement stat, FlattenStatementsHelper flatthelper, Map<String, VarExprent> map) {

    List<VarExprent> lst = null;

    if (stat instanceof CatchAllStatement) {
      CatchAllStatement catchall = (CatchAllStatement)stat;
      if (!catchall.isFinally()) {
        lst = catchall.getVars();
      }
    }
    else if (stat instanceof CatchStatement) {
      lst = ((CatchStatement)stat).getVars();
    }

    if (lst != null) {
      for (int i = 1; i < stat.getStats().size(); i++) {
        map.put(flatthelper.getDirectNode(stat.getStats().get(i)).id, lst.get(i - 1));
      }
    }

    for (Statement st : stat.getStats()) {
      collectCatchVars(st, flatthelper, map);
    }
  }

  private static void initStatementExprents(Statement stat) {
    stat.initExprents();

    for (Statement st : stat.getStats()) {
      initStatementExprents(st);
    }
  }

  public void processBlock(BasicBlockStatement stat, PrimitiveExprsList data, StructClass cl) {

    ConstantPool pool = cl.getPool();
    StructBootstrapMethodsAttribute bootstrap = cl.getAttribute(StructGeneralAttribute.ATTRIBUTE_BOOTSTRAP_METHODS);

    BasicBlock block = stat.getBlock();

    ListStack<Exprent> stack = data.getStack();
    List<Exprent> exprlist = data.getLstExprents();

    InstructionSequence seq = block.getSeq();

    // RTF: temporary storage for popped expression preceding an INVOKESTATIC,
    // used to preserve instance-qualified static method calls.
    Exprent rtfStaticInstanceQualifier = null;
    // RTF: string-based qualifier for cases where args are loaded between POP and INVOKESTATIC.
    // The string is pre-rendered at POP time to avoid corruption by later decompiler passes.
    String rtfStaticInstanceQualifierStr = null;
    int rtfStaticQualifierTargetIdx = -1;

    for (int i = 0; i < seq.length(); i++) {

      Instruction instr = seq.getInstr(i);
      Integer bytecode_offset = block.getOldOffset(i);
      BitSet bytecode_offsets = null;
      if (bytecode_offset >= 0) {
        bytecode_offsets = new BitSet();
        bytecode_offsets.set(bytecode_offset, bytecode_offset + instr.length);
      }

      switch (instr.opcode) {
        case opc_aconst_null:
          pushEx(stack, exprlist, new ConstExprent(VarType.VARTYPE_NULL, null, bytecode_offsets));
          break;
        case opc_bipush:
        case opc_sipush:
          pushEx(stack, exprlist, new ConstExprent(instr.operand(0), true, bytecode_offsets));
          break;
        case opc_lconst_0:
        case opc_lconst_1:
          pushEx(stack, exprlist, new ConstExprent(VarType.VARTYPE_LONG, (long)(instr.opcode - opc_lconst_0), bytecode_offsets));
          break;
        case opc_fconst_0:
        case opc_fconst_1:
        case opc_fconst_2:
          pushEx(stack, exprlist, new ConstExprent(VarType.VARTYPE_FLOAT, (float)(instr.opcode - opc_fconst_0), bytecode_offsets));
          break;
        case opc_dconst_0:
        case opc_dconst_1:
          pushEx(stack, exprlist, new ConstExprent(VarType.VARTYPE_DOUBLE, (double)(instr.opcode - opc_dconst_0), bytecode_offsets));
          break;
        case opc_ldc:
        case opc_ldc_w:
        case opc_ldc2_w:
          PooledConstant cn = pool.getConstant(instr.operand(0));
          if (cn instanceof PrimitiveConstant) {
            pushEx(stack, exprlist, new ConstExprent(consts[cn.type - CONSTANT_Integer], ((PrimitiveConstant)cn).value, bytecode_offsets));
          }
          else if (cn instanceof LinkConstant && cn.type == CodeConstants.CONSTANT_Dynamic) {
            LinkConstant invoke_constant = (LinkConstant) cn;

            LinkConstant bootstrapMethod = null;
            List<PooledConstant> bootstrap_arguments = null;
            if (bootstrap != null) {
              bootstrapMethod = bootstrap.getMethodReference(invoke_constant.index1);
              bootstrap_arguments = bootstrap.getMethodArguments(invoke_constant.index1);
            }

            InvocationExprent exprinv = new InvocationExprent(instr.opcode, invoke_constant, bootstrapMethod, bootstrap_arguments, stack, bytecode_offsets);
            if (exprinv.getDescriptor().ret.type == CodeType.VOID) {
              exprlist.add(exprinv);
            }
            else {
              pushEx(stack, exprlist, CondyHelper.simplifyCondy(exprinv));
            }
          }
          else if (cn instanceof LinkConstant) {
            //TODO: for now treat Links as Strings
            pushEx(stack, exprlist, new ConstExprent(VarType.VARTYPE_STRING, ((LinkConstant)cn).elementname, bytecode_offsets));
          }
          break;
        case opc_iload:
        case opc_lload:
        case opc_fload:
        case opc_dload:
        case opc_aload:
          VarExprent varExprent = new VarExprent(instr.operand(0), varTypes[instr.opcode - opc_iload], varProcessor, bytecode_offsets);
          varExprent.setBackingInstr(instr);
          varProcessor.findLVT(varExprent, bytecode_offset + instr.length);
          pushEx(stack, exprlist, varExprent);
          break;
        case opc_iaload:
        case opc_laload:
        case opc_faload:
        case opc_daload:
        case opc_aaload:
        case opc_baload:
        case opc_caload:
        case opc_saload:
          Exprent index = stack.pop();
          Exprent arr = stack.pop();

          VarType vartype = null;
          switch (instr.opcode) {
            case opc_laload:
              vartype = VarType.VARTYPE_LONG;
              break;
            case opc_daload:
              vartype = VarType.VARTYPE_DOUBLE;
          }
          pushEx(stack, exprlist, new ArrayExprent(arr, index, arrTypes[instr.opcode - opc_iaload], bytecode_offsets), vartype);
          break;
        case opc_istore:
        case opc_lstore:
        case opc_fstore:
        case opc_dstore:
        case opc_astore:
          Exprent expr = stack.pop();
          int varindex = instr.operand(0);
          if (bytecode_offsets != null) { //TODO: Figure out why this nulls in some cases
            bytecode_offsets.set(bytecode_offset, bytecode_offset + instr.length);
          }
          varExprent = new VarExprent(varindex, varTypes[instr.opcode - opc_istore], varProcessor, bytecode_offsets);
          varExprent.setBackingInstr(instr);
          varProcessor.findLVT(varExprent, bytecode_offset + instr.length);
          AssignmentExprent assign = new AssignmentExprent(varExprent, expr, bytecode_offsets);
          exprlist.add(assign);
          break;
        case opc_iastore:
        case opc_lastore:
        case opc_fastore:
        case opc_dastore:
        case opc_aastore:
        case opc_bastore:
        case opc_castore:
        case opc_sastore:
          Exprent value = stack.pop();
          Exprent index_store = stack.pop();
          Exprent arr_store = stack.pop();
          AssignmentExprent arrassign =
            new AssignmentExprent(new ArrayExprent(arr_store, index_store, arrTypes[instr.opcode - opc_iastore], bytecode_offsets), value,
                                  bytecode_offsets);
          exprlist.add(arrassign);
          break;
        case opc_iadd:
        case opc_ladd:
        case opc_fadd:
        case opc_dadd:
        case opc_isub:
        case opc_lsub:
        case opc_fsub:
        case opc_dsub:
        case opc_imul:
        case opc_lmul:
        case opc_fmul:
        case opc_dmul:
        case opc_idiv:
        case opc_ldiv:
        case opc_fdiv:
        case opc_ddiv:
        case opc_irem:
        case opc_lrem:
        case opc_frem:
        case opc_drem:
          pushEx(stack, exprlist, new FunctionExprent(func1[(instr.opcode - opc_iadd) / 4], stack, bytecode_offsets));
          break;
        case opc_ishl:
        case opc_lshl:
        case opc_ishr:
        case opc_lshr:
        case opc_iushr:
        case opc_lushr:
        case opc_iand:
        case opc_land:
        case opc_ior:
        case opc_lor:
        case opc_ixor:
        case opc_lxor:
          pushEx(stack, exprlist, new FunctionExprent(func2[(instr.opcode - opc_ishl) / 2], stack, bytecode_offsets));
          break;
        case opc_ineg:
        case opc_lneg:
        case opc_fneg:
        case opc_dneg:
          pushEx(stack, exprlist, new FunctionExprent(FunctionType.NEG, stack, bytecode_offsets));
          break;
        case opc_iinc:
          VarExprent vevar = new VarExprent(instr.operand(0), VarType.VARTYPE_INT, varProcessor, bytecode_offsets);
          vevar.setBackingInstr(instr);
          varProcessor.findLVT(vevar, bytecode_offset + instr.length);
          exprlist.add(new AssignmentExprent(vevar, new FunctionExprent(
            instr.operand(1) < 0 ? FunctionType.SUB : FunctionType.ADD, Arrays
            .asList(vevar.copy(), new ConstExprent(VarType.VARTYPE_INT, Math.abs(instr.operand(1)), null)),
            bytecode_offsets), bytecode_offsets));
          break;
        case opc_i2l:
        case opc_i2f:
        case opc_i2d:
        case opc_l2i:
        case opc_l2f:
        case opc_l2d:
        case opc_f2i:
        case opc_f2l:
        case opc_f2d:
        case opc_d2i:
        case opc_d2l:
        case opc_d2f:
        case opc_i2b:
        case opc_i2c:
        case opc_i2s:
          pushEx(stack, exprlist, new FunctionExprent(func3[instr.opcode - opc_i2l], stack, bytecode_offsets));
          break;
        case opc_lcmp:
        case opc_fcmpl:
        case opc_fcmpg:
        case opc_dcmpl:
        case opc_dcmpg:
          pushEx(stack, exprlist, new FunctionExprent(func4[instr.opcode - opc_lcmp], stack, bytecode_offsets));
          break;
        case opc_ifeq:
        case opc_ifne:
        case opc_iflt:
        case opc_ifge:
        case opc_ifgt:
        case opc_ifle:
          exprlist.add(new IfExprent(func5[instr.opcode - opc_ifeq].getNegative(), stack, bytecode_offsets));
          break;
        case opc_if_icmpeq:
        case opc_if_icmpne:
        case opc_if_icmplt:
        case opc_if_icmpge:
        case opc_if_icmpgt:
        case opc_if_icmple:
        case opc_if_acmpeq:
        case opc_if_acmpne:
          exprlist.add(new IfExprent(func6[instr.opcode - opc_if_icmpeq].getNegative(), stack, bytecode_offsets));
          break;
        case opc_ifnull:
        case opc_ifnonnull:
          exprlist.add(new IfExprent(func7[instr.opcode - opc_ifnull].getNegative(), stack, bytecode_offsets));
          break;
        case opc_tableswitch:
        case opc_lookupswitch:
          exprlist.add(new SwitchHeadExprent(stack.pop(), bytecode_offsets));
          break;
        case opc_ireturn:
        case opc_lreturn:
        case opc_freturn:
        case opc_dreturn:
        case opc_areturn:
        case opc_return:
        case opc_athrow:
          exprlist.add(new ExitExprent(instr.opcode == opc_athrow ? ExitExprent.Type.THROW : ExitExprent.Type.RETURN,
                                       instr.opcode == opc_return ? null : stack.pop(),
                                       instr.opcode == opc_athrow ? null : methodDescriptor.ret,
                                       bytecode_offsets, methodDescriptor));
          break;
        case opc_monitorenter:
        case opc_monitorexit:
          MonitorExprent monitor = new MonitorExprent(func8[instr.opcode - opc_monitorenter], stack.pop(), bytecode_offsets);

          if (instr.opcode == opc_monitorexit && stat.isRemovableMonitorexit()) {
            monitor.setRemove(true);
          }

          exprlist.add(monitor);
          break;
        case opc_checkcast:
        case opc_instanceof:
          stack.push(new ConstExprent(new VarType(pool.getPrimitiveConstant(instr.operand(0)).getString(), true), null, null));
        case opc_arraylength:
          pushEx(stack, exprlist, new FunctionExprent(mapConsts.get(instr.opcode), stack, bytecode_offsets));
          break;
        case opc_getstatic:
        case opc_getfield:
          pushEx(stack, exprlist,
                 new FieldExprent(pool.getLinkConstant(instr.operand(0)), instr.opcode == opc_getstatic ? null : stack.pop(),
                                  bytecode_offsets));
          break;
        case opc_putstatic:
        case opc_putfield:
          Exprent valfield = stack.pop();
          Exprent exprfield =
            new FieldExprent(pool.getLinkConstant(instr.operand(0)), instr.opcode == opc_putstatic ? null : stack.pop(),
                             bytecode_offsets);
          exprlist.add(new AssignmentExprent(exprfield, valfield, bytecode_offsets));
          break;
        case opc_invokevirtual:
        case opc_invokespecial:
        case opc_invokestatic:
        case opc_invokeinterface:
        case opc_invokedynamic:
          if (instr.opcode != opc_invokedynamic || instr.bytecodeVersion.hasInvokeDynamic()) {
            LinkConstant invoke_constant = pool.getLinkConstant(instr.operand(0));

            LinkConstant bootstrapMethod = null;
            List<PooledConstant> bootstrap_arguments = null;
            if (instr.opcode == opc_invokedynamic && bootstrap != null) {
              bootstrapMethod = bootstrap.getMethodReference(invoke_constant.index1);
              bootstrap_arguments = bootstrap.getMethodArguments(invoke_constant.index1);
            }

            InvocationExprent exprinv = new InvocationExprent(instr.opcode, invoke_constant, bootstrapMethod, bootstrap_arguments, stack, bytecode_offsets);
            // RTF: attach the saved instance qualifier from a preceding POP to this INVOKESTATIC
            if (rtfStaticInstanceQualifier != null && instr.opcode == opc_invokestatic) {
              exprinv.setStaticInstanceQualifier(rtfStaticInstanceQualifier);
              rtfStaticInstanceQualifier = null;
            }
            // RTF: attach string-based qualifier for gap case (args between POP and INVOKESTATIC)
            if (rtfStaticInstanceQualifierStr != null && i == rtfStaticQualifierTargetIdx && instr.opcode == opc_invokestatic) {
              exprinv.setStaticInstanceQualifierString(rtfStaticInstanceQualifierStr);
              rtfStaticInstanceQualifierStr = null;
              rtfStaticQualifierTargetIdx = -1;
            }
            if (exprinv.getDescriptor().ret.type == CodeType.VOID) {
              exprlist.add(exprinv);
            }
            else {
              pushEx(stack, exprlist, exprinv);
            }
          }
          break;
        case opc_new:
        case opc_anewarray:
        case opc_multianewarray:
          int dimensions = (instr.opcode == opc_new) ? 0 : (instr.opcode == opc_anewarray) ? 1 : instr.operand(1);
          VarType arrType = new VarType(pool.getPrimitiveConstant(instr.operand(0)).getString(), true);
          if (instr.opcode != opc_multianewarray) {
            arrType = arrType.resizeArrayDim(arrType.arrayDim + dimensions);
          }
          pushEx(stack, exprlist, new NewExprent(arrType, stack, dimensions, bytecode_offsets));
          break;
        case opc_newarray:
          pushEx(stack, exprlist, new NewExprent(new VarType(arrTypeIds[instr.operand(0) - 4], 1), stack, 1, bytecode_offsets));
          break;
        case opc_dup:
          pushEx(stack, exprlist, stack.getByOffset(-1).copy());
          break;
        case opc_dup_x1:
          insertByOffsetEx(-2, stack, exprlist, -1);
          break;
        case opc_dup_x2:
          if (stack.getByOffset(-2).getExprType().stackSize == 2) {
            insertByOffsetEx(-2, stack, exprlist, -1);
          }
          else {
            insertByOffsetEx(-3, stack, exprlist, -1);
          }
          break;
        case opc_dup2:
          if (stack.getByOffset(-1).getExprType().stackSize == 2) {
            pushEx(stack, exprlist, stack.getByOffset(-1).copy());
          }
          else {
            pushEx(stack, exprlist, stack.getByOffset(-2).copy());
            pushEx(stack, exprlist, stack.getByOffset(-2).copy());
          }
          break;
        case opc_dup2_x1:
          if (stack.getByOffset(-1).getExprType().stackSize == 2) {
            insertByOffsetEx(-2, stack, exprlist, -1);
          }
          else {
            insertByOffsetEx(-3, stack, exprlist, -2);
            insertByOffsetEx(-3, stack, exprlist, -1);
          }
          break;
        case opc_dup2_x2:
          if (stack.getByOffset(-1).getExprType().stackSize == 2) {
            if (stack.getByOffset(-2).getExprType().stackSize == 2) {
              insertByOffsetEx(-2, stack, exprlist, -1);
            }
            else {
              insertByOffsetEx(-3, stack, exprlist, -1);
            }
          }
          else {
            if (stack.getByOffset(-3).getExprType().stackSize == 2) {
              insertByOffsetEx(-3, stack, exprlist, -2);
              insertByOffsetEx(-3, stack, exprlist, -1);
            }
            else {
              insertByOffsetEx(-4, stack, exprlist, -2);
              insertByOffsetEx(-4, stack, exprlist, -1);
            }
          }
          break;
        case opc_swap:
          insertByOffsetEx(-2, stack, exprlist, -1);
          stack.pop();
          break;
        case opc_pop:
          // RTF: detect GETFIELD/ALOAD + POP + INVOKESTATIC pattern to preserve
          // instance-qualified static calls (e.g., this.field.staticMethod()).
          // pushEx wraps ALL expressions in stack variables, so stack.pop() always
          // returns VarExprent. We must look at the DEFINITION (the assignment RHS
          // in exprlist) to determine if the source was a field/variable load vs
          // a method return value. Only field/variable loads are valid qualifiers.
          //
          // Two cases:
          // 1. Immediate: POP is directly followed by INVOKESTATIC (i+1) - use Exprent approach
          // 2. Gap: args are loaded between POP and INVOKESTATIC - use String approach
          //    (string avoids corruption by later variable renaming/merging passes)
          if (DecompilerContext.isRoundtripFidelity() && !exprlist.isEmpty()) {
            Exprent lastExpr = exprlist.get(exprlist.size() - 1);
            Exprent rhs = null;
            if (lastExpr instanceof AssignmentExprent) {
              Exprent rhsCandidate = ((AssignmentExprent) lastExpr).getRight();
              if (rhsCandidate instanceof FieldExprent ||
                  (rhsCandidate instanceof VarExprent && !((VarExprent) rhsCandidate).isStack())) {
                rhs = rhsCandidate;
              }
            }
            if (rhs != null && i + 1 < seq.length() && seq.getInstr(i + 1).opcode == opc_invokestatic) {
              // Case 1: immediate - POP followed directly by INVOKESTATIC
              Exprent popped = stack.pop();
              String staticMethodClass = pool.getLinkConstant(seq.getInstr(i + 1).operand(0)).classname;
              if (validateQualifierForStaticCall(rhs, staticMethodClass)) {
                rtfStaticInstanceQualifier = popped;
              }
            } else if (rhs != null && i + 1 < seq.length()) {
              // Case 2: gap - args loaded between POP and INVOKESTATIC.
              // Validate backward: the instruction before POP must be GETFIELD (for field qualifier)
              // or a load instruction (for "this" qualifier). This prevents false positives where
              // a POP discards an unrelated expression.
              boolean validBackwardPattern = false;
              if (i >= 1) {
                int prevOpc = seq.getInstr(i - 1).opcode;
                if (rhs instanceof FieldExprent && prevOpc == opc_getfield) {
                  validBackwardPattern = true;
                } else if (rhs instanceof VarExprent && (prevOpc == opc_aload
                    || (prevOpc >= opc_aload_0 && prevOpc <= opc_aload_3))) {
                  validBackwardPattern = true;
                }
              }
              if (validBackwardPattern) {
                String qualifierClassName = null;
                if (rhs instanceof FieldExprent) {
                  qualifierClassName = ((FieldExprent) rhs).getDescriptor().type.value;
                } else if (rhs instanceof VarExprent && ((VarExprent) rhs).getIndex() == 0) {
                  StructClass currentClass = DecompilerContext.getContextProperty(DecompilerContext.CURRENT_CLASS);
                  if (currentClass != null) {
                    qualifierClassName = currentClass.qualifiedName;
                  }
                }
                if (qualifierClassName != null) {
                  int targetIdx = findStaticCallAfterPop(seq, i, pool, qualifierClassName);
                  if (targetIdx >= 0) {
                    String qualStr = renderQualifierToString(rhs, exprlist);
                    if (qualStr != null) {
                      stack.pop();
                      rtfStaticInstanceQualifierStr = qualStr;
                      rtfStaticQualifierTargetIdx = targetIdx;
                    } else {
                      stack.pop();
                    }
                  } else {
                    stack.pop();
                  }
                } else {
                  stack.pop();
                }
              } else {
                stack.pop();
              }
            } else {
              stack.pop();
            }
          } else {
            stack.pop();
          }
          // check for synthetic getClass and requireNonNull calls added by the compiler
          // see https://stackoverflow.com/a/20130641
          if (!exprlist.isEmpty()) {
            Exprent last = exprlist.get(exprlist.size() - 1);
            // Our heuristic is checking for an assignment and the type of the assignment is an invocation.
            // This roughly corresponds to a pattern of DUP [nullcheck] POP.
            if (last instanceof AssignmentExprent && ((AssignmentExprent)last).getRight() instanceof InvocationExprent) {
              InvocationExprent invocation = (InvocationExprent) ((AssignmentExprent) last).getRight();

              // Check to make sure there's still more opcodes after this one
              if (i + 1 < seq.length()) {
                // Match either this.getClass() or Objects.requireNonNull([value]);
                if ((!invocation.isStatic() && invocation.getName().equals("getClass") && invocation.getStringDescriptor().equals("()Ljava/lang/Class;")) // J8
                  || (invocation.isStatic() && invocation.getClassname().equals("java/util/Objects") && invocation.getName().equals("requireNonNull") && invocation.getStringDescriptor().equals("(Ljava/lang/Object;)Ljava/lang/Object;"))) { // J9+

                  // Ensure that these null checks are constant loads, LDC opcodes, null loads, or bi/sipushes.
                  int nextOpc = seq.getInstr(i + 1).opcode;
                  if (nextOpc >= opc_aconst_null && nextOpc <= opc_ldc2_w) {
                    invocation.setSyntheticNullCheck();
                  }
                }
              }
            }
          }
          break;
        case opc_pop2:
          if (stack.getByOffset(-1).getExprType().stackSize == 1) {
            // Since value at the top of the stack is a value of category 1 (JVMS9 2.11.1)
            // we should remove one more item from the stack.
            // See JVMS9 pop2 chapter.
            stack.pop();
          }
          stack.pop();
          break;
      }
    }
  }

  /**
   * RTF: Scan forward from a POP instruction to find the matching INVOKESTATIC that
   * consumes the arguments loaded between POP and the call. Returns the instruction
   * index of the target INVOKESTATIC, or -1 if no match found.
   *
   * After POP, the stack depth relative to the POP point is 0. Each subsequent instruction
   * changes the depth. When we find an INVOKESTATIC whose parameter slot count equals the
   * current depth, that is the target (the arguments loaded since POP are exactly its params).
   *
   * We also validate the INVOKESTATIC's declaring class matches the qualifier type.
   */
  private int findStaticCallAfterPop(InstructionSequence seq, int popIndex, ConstantPool pool,
                                     String qualifierClassName) {
    int depth = 0;
    for (int j = popIndex + 1; j < seq.length(); j++) {
      Instruction instr = seq.getInstr(j);
      int opc = instr.opcode;

      // Control flow instructions abort the scan
      if ((opc >= opc_ifeq && opc <= opc_if_acmpne) || opc == opc_ifnull || opc == opc_ifnonnull
          || opc == opc_goto || opc == opc_goto_w || opc == opc_jsr || opc == opc_jsr_w
          || opc == opc_ret || opc == opc_tableswitch || opc == opc_lookupswitch
          || (opc >= opc_ireturn && opc <= opc_return) || opc == opc_athrow) {
        return -1;
      }

      if (opc == opc_invokestatic) {
        LinkConstant lc = pool.getLinkConstant(instr.operand(0));
        MethodDescriptor md = MethodDescriptor.parseDescriptor(lc.descriptor);
        int paramSlots = 0;
        for (VarType p : md.params) {
          paramSlots += p.stackSize;
        }
        if (depth == paramSlots && lc.classname.equals(qualifierClassName)) {
          return j;
        }
        // INVOKESTATIC that doesn't match: adjust depth for its effect
        int retSlots = (md.ret.type == CodeType.VOID) ? 0 : md.ret.stackSize;
        depth = depth - paramSlots + retSlots;
      } else {
        // Compute stack delta for this instruction
        int delta = computeStackDelta(instr, pool);
        if (delta == Integer.MIN_VALUE) {
          return -1; // unknown instruction, abort
        }
        depth += delta;
      }

      if (depth < 0) {
        return -1; // underflow, something is wrong
      }
    }
    return -1;
  }

  /**
   * RTF: Compute the net stack delta for a single bytecode instruction.
   * Returns Integer.MIN_VALUE for instructions that cannot be handled.
   */
  private static int computeStackDelta(Instruction instr, ConstantPool pool) {
    int opc = instr.opcode;

    // Loads push 1 slot (or 2 for long/double)
    if (opc == opc_aload || (opc >= opc_aload_0 && opc <= opc_aload_3)) return 1;
    if (opc == opc_iload || (opc >= opc_iload_0 && opc <= opc_iload_3)) return 1;
    if (opc == opc_fload || (opc >= opc_fload_0 && opc <= opc_fload_3)) return 1;
    if (opc == opc_lload || (opc >= opc_lload_0 && opc <= opc_lload_3)) return 2;
    if (opc == opc_dload || (opc >= opc_dload_0 && opc <= opc_dload_3)) return 2;

    // Stores pop 1 slot (or 2)
    if (opc == opc_astore || (opc >= opc_astore_0 && opc <= opc_astore_3)) return -1;
    if (opc == opc_istore || (opc >= opc_istore_0 && opc <= opc_istore_3)) return -1;
    if (opc == opc_fstore || (opc >= opc_fstore_0 && opc <= opc_fstore_3)) return -1;
    if (opc == opc_lstore || (opc >= opc_lstore_0 && opc <= opc_lstore_3)) return -2;
    if (opc == opc_dstore || (opc >= opc_dstore_0 && opc <= opc_dstore_3)) return -2;

    // Constants
    if (opc == opc_aconst_null) return 1;
    if (opc >= opc_iconst_m1 && opc <= opc_iconst_5) return 1;
    if (opc == opc_lconst_0 || opc == opc_lconst_1) return 2;
    if (opc >= opc_fconst_0 && opc <= opc_fconst_2) return 1;
    if (opc == opc_dconst_0 || opc == opc_dconst_1) return 2;
    if (opc == opc_bipush || opc == opc_sipush) return 1;

    // LDC: depends on the constant type
    if (opc == opc_ldc || opc == opc_ldc_w) return 1;
    if (opc == opc_ldc2_w) return 2;

    // Field access
    if (opc == opc_getfield) {
      // pops objectref, pushes field value
      FieldDescriptor fd = FieldDescriptor.parseDescriptor(pool.getLinkConstant(instr.operand(0)).descriptor);
      return -1 + fd.type.stackSize;
    }
    if (opc == opc_getstatic) {
      FieldDescriptor fd = FieldDescriptor.parseDescriptor(pool.getLinkConstant(instr.operand(0)).descriptor);
      return fd.type.stackSize;
    }
    if (opc == opc_putfield) {
      FieldDescriptor fd = FieldDescriptor.parseDescriptor(pool.getLinkConstant(instr.operand(0)).descriptor);
      return -1 - fd.type.stackSize;
    }
    if (opc == opc_putstatic) {
      FieldDescriptor fd = FieldDescriptor.parseDescriptor(pool.getLinkConstant(instr.operand(0)).descriptor);
      return -fd.type.stackSize;
    }

    // Invoke (non-static handled here; invokestatic handled in the caller)
    if (opc == opc_invokevirtual || opc == opc_invokespecial || opc == opc_invokeinterface) {
      LinkConstant lc = pool.getLinkConstant(instr.operand(0));
      MethodDescriptor md = MethodDescriptor.parseDescriptor(lc.descriptor);
      int paramSlots = 0;
      for (VarType p : md.params) {
        paramSlots += p.stackSize;
      }
      int retSlots = (md.ret.type == CodeType.VOID) ? 0 : md.ret.stackSize;
      return -(paramSlots + 1) + retSlots; // +1 for objectref
    }

    // DUP variants
    if (opc == opc_dup) return 1;
    if (opc == opc_dup_x1) return 1;
    if (opc == opc_dup_x2) return 1;
    if (opc == opc_dup2) return 2;
    if (opc == opc_dup2_x1) return 2;
    if (opc == opc_dup2_x2) return 2;
    if (opc == opc_swap) return 0;
    if (opc == opc_pop) return -1;
    if (opc == opc_pop2) return -2;

    // Arithmetic and type conversions: same-size in, same-size out
    // Binary int ops: pop 2, push 1 => -1
    if ((opc >= opc_iadd && opc <= opc_irem) && (opc - opc_iadd) % 4 == 0) return -1; // iadd, isub, imul, idiv, irem
    if ((opc >= opc_iadd && opc <= opc_drem) && ((opc - opc_iadd) % 4 == 1)) return -2; // ladd, lsub, lmul, ldiv, lrem
    if ((opc >= opc_iadd && opc <= opc_drem) && ((opc - opc_iadd) % 4 == 2)) return -1; // fadd, fsub, fmul, fdiv, frem
    if ((opc >= opc_iadd && opc <= opc_drem) && ((opc - opc_iadd) % 4 == 3)) return -2; // dadd, dsub, dmul, ddiv, drem

    // Unary negate: no change in stack size
    if (opc == opc_ineg || opc == opc_fneg) return 0;
    if (opc == opc_lneg || opc == opc_dneg) return 0;

    // Shift ops
    if (opc == opc_ishl || opc == opc_ishr || opc == opc_iushr) return -1;
    if (opc == opc_lshl || opc == opc_lshr || opc == opc_lushr) return -1; // long shift: pop long+int, push long
    // Bitwise ops
    if (opc == opc_iand || opc == opc_ior || opc == opc_ixor) return -1;
    if (opc == opc_land || opc == opc_lor || opc == opc_lxor) return -2;

    // iinc: no stack effect
    if (opc == opc_iinc) return 0;

    // Type conversions
    if (opc == opc_i2l) return 1;   // int->long: +1 slot
    if (opc == opc_i2f) return 0;   // int->float: same
    if (opc == opc_i2d) return 1;   // int->double: +1 slot
    if (opc == opc_l2i) return -1;  // long->int: -1 slot
    if (opc == opc_l2f) return -1;  // long->float: -1 slot
    if (opc == opc_l2d) return 0;   // long->double: same (2 slots)
    if (opc == opc_f2i) return 0;   // float->int: same
    if (opc == opc_f2l) return 1;   // float->long: +1 slot
    if (opc == opc_f2d) return 1;   // float->double: +1 slot
    if (opc == opc_d2i) return -1;  // double->int: -1 slot
    if (opc == opc_d2l) return 0;   // double->long: same (2 slots)
    if (opc == opc_d2f) return -1;  // double->float: -1 slot
    if (opc == opc_i2b || opc == opc_i2c || opc == opc_i2s) return 0;

    // Comparison ops
    if (opc == opc_lcmp) return -3;  // pop 2 longs (4 slots), push int (1 slot)
    if (opc == opc_fcmpl || opc == opc_fcmpg) return -1;  // pop 2 floats, push int
    if (opc == opc_dcmpl || opc == opc_dcmpg) return -3;  // pop 2 doubles (4 slots), push int

    // Object operations
    if (opc == opc_new) return 1;
    if (opc == opc_newarray || opc == opc_anewarray) return 0; // pop count, push array
    if (opc == opc_arraylength) return 0; // pop arrayref, push int
    if (opc == opc_checkcast) return 0;
    if (opc == opc_instanceof) return 0; // pop objectref, push int
    if (opc == opc_monitorenter || opc == opc_monitorexit) return -1;
    if (opc == opc_multianewarray) return -(instr.operand(1)) + 1; // pop N dimensions, push array

    // Array load: pop 2 (arrayref + index), push value
    if (opc == opc_iaload || opc == opc_faload || opc == opc_aaload
        || opc == opc_baload || opc == opc_caload || opc == opc_saload) return -1;
    if (opc == opc_laload || opc == opc_daload) return 0; // pop 2 slots, push 2 slots

    // Array store: pop 2/3 + value
    if (opc == opc_iastore || opc == opc_fastore || opc == opc_aastore
        || opc == opc_bastore || opc == opc_castore || opc == opc_sastore) return -3;
    if (opc == opc_lastore || opc == opc_dastore) return -4;

    // NOP
    if (opc == opc_nop) return 0;

    // invokedynamic
    if (opc == opc_invokedynamic) {
      LinkConstant lc = pool.getLinkConstant(instr.operand(0));
      MethodDescriptor md = MethodDescriptor.parseDescriptor(lc.descriptor);
      int paramSlots = 0;
      for (VarType p : md.params) {
        paramSlots += p.stackSize;
      }
      int retSlots = (md.ret.type == CodeType.VOID) ? 0 : md.ret.stackSize;
      return -paramSlots + retSlots;
    }

    return Integer.MIN_VALUE; // unknown
  }

  /**
   * RTF: Validate that the qualifier expression (the RHS of the assignment before POP)
   * matches the declaring class of the static method. Returns true if the qualifier is valid.
   */
  private static boolean validateQualifierForStaticCall(Exprent rhs, String staticMethodClass) {
    if (rhs instanceof VarExprent && ((VarExprent) rhs).getIndex() == 0) {
      // "this" qualifier
      StructClass currentClass = DecompilerContext.getContextProperty(DecompilerContext.CURRENT_CLASS);
      return currentClass != null && currentClass.qualifiedName.equals(staticMethodClass);
    } else if (rhs instanceof FieldExprent) {
      String fieldTypeName = ((FieldExprent) rhs).getDescriptor().type.value;
      return staticMethodClass.equals(fieldTypeName);
    }
    return false;
  }

  /**
   * RTF: Render the qualifier expression to a Java string for use as a static instance qualifier.
   * Only handles patterns that resolve to "this" or "this.fieldName".
   * Returns null if the pattern cannot be resolved to a known qualifier.
   *
   * Note: stack variable indices are reused (STACK_BASE + stack.size()), so a GETFIELD that
   * pops-then-pushes can reuse the same index as the preceding ALOAD. This means exprlist
   * can contain: stack_N = VarExprent(0); stack_N = FieldExprent(clim, stack_N).
   * When resolving the FieldExprent's instance (stack_N), we must skip past the
   * FieldExprent's own assignment to find the earlier ALOAD assignment.
   */
  private static String renderQualifierToString(Exprent rhs, List<Exprent> exprlist) {
    if (rhs instanceof VarExprent && ((VarExprent) rhs).getIndex() == 0) {
      return "this";
    } else if (rhs instanceof FieldExprent) {
      FieldExprent field = (FieldExprent) rhs;
      Exprent instance = field.getInstance();
      String fieldName = field.getName();

      // Find the position of the last assignment (the FieldExprent's own) in exprlist.
      // We need to search BEFORE this position for the instance definition.
      int startSearch = exprlist.size() - 1;
      if (instance instanceof VarExprent && ((VarExprent) instance).isStack()) {
        int targetIdx = ((VarExprent) instance).getIndex();
        // The last assignment to targetIdx is the FieldExprent's own.
        // Find it and start searching before it.
        for (int k = exprlist.size() - 1; k >= 0; k--) {
          Exprent e = exprlist.get(k);
          if (e instanceof AssignmentExprent) {
            Exprent lhs = ((AssignmentExprent) e).getLeft();
            if (lhs instanceof VarExprent && ((VarExprent) lhs).getIndex() == targetIdx) {
              startSearch = k - 1;
              break;
            }
          }
        }
      }
      // Resolve the instance from startSearch backward
      String instanceStr = resolveInstanceToThis(instance, exprlist, startSearch);
      if (instanceStr != null) {
        return instanceStr + "." + fieldName;
      }
    }
    return null; // cannot resolve - do not store qualifier
  }

  /**
   * RTF: Trace a stack variable back through exprlist to check if it originates from "this".
   * Returns "this" if it does, null otherwise. Only follows simple assignment chains
   * (max 10 hops) to avoid runaway recursion.
   * @param searchFrom the index in exprlist to start searching from (inclusive)
   */
  private static String resolveInstanceToThis(Exprent expr, List<Exprent> exprlist, int searchFrom) {
    int hops = 0;
    while (hops < 10) {
      if (expr instanceof VarExprent) {
        VarExprent var = (VarExprent) expr;
        if (var.getIndex() == 0 && !var.isStack()) {
          return "this";
        }
        if (!var.isStack()) {
          return null; // non-stack, non-this variable
        }
        // Find the definition of this stack variable in exprlist, starting from searchFrom
        Exprent resolved = null;
        int foundAt = -1;
        for (int k = Math.min(searchFrom, exprlist.size() - 1); k >= 0; k--) {
          Exprent e = exprlist.get(k);
          if (e instanceof AssignmentExprent) {
            Exprent lhs = ((AssignmentExprent) e).getLeft();
            if (lhs instanceof VarExprent && ((VarExprent) lhs).getIndex() == var.getIndex()) {
              resolved = ((AssignmentExprent) e).getRight();
              foundAt = k;
              break;
            }
          }
        }
        if (resolved == null) {
          return null; // definition not found
        }
        expr = resolved;
        searchFrom = foundAt - 1; // for next hop, search before this definition
        hops++;
      } else {
        return null; // not a simple var chain
      }
    }
    return null; // too many hops
  }

  private void pushEx(ListStack<Exprent> stack, List<Exprent> exprlist, Exprent exprent) {
    pushEx(stack, exprlist, exprent, null);
  }

  private void pushEx(ListStack<Exprent> stack, List<Exprent> exprlist, Exprent exprent, VarType vartype) {
    ValidationHelper.notNull(exprent);

    int varindex = VarExprent.STACK_BASE + stack.size();
    VarExprent var = new VarExprent(varindex, vartype == null ? exprent.getExprType() : vartype, varProcessor);
    var.setStack(true);

    exprlist.add(new AssignmentExprent(var, exprent, null));
    stack.push(var.copy());
  }

  private void insertByOffsetEx(int offset, ListStack<Exprent> stack, List<Exprent> exprlist, int copyoffset) {

    int base = VarExprent.STACK_BASE + stack.size();

    LinkedList<VarExprent> lst = new LinkedList<>();

    for (int i = -1; i >= offset; i--) {
      Exprent varex = stack.pop();
      VarExprent varnew = new VarExprent(base + i + 1, varex.getExprType(), varProcessor);
      varnew.setStack(true);
      exprlist.add(new AssignmentExprent(varnew, varex, null));
      lst.add(0, (VarExprent)varnew.copy());
    }

    Exprent exprent = lst.get(lst.size() + copyoffset).copy();
    VarExprent var = new VarExprent(base + offset, exprent.getExprType(), varProcessor);
    var.setStack(true);
    exprlist.add(new AssignmentExprent(var, exprent, null));
    lst.add(0, (VarExprent)var.copy());

    for (VarExprent expr : lst) {
      stack.push(expr);
    }
  }

  public static boolean canonicalizeCasts(RootStatement stat) {
    boolean res = false;
    while (canonicalizeCasts((Statement) stat)) {
      res = true;
    }

    return res;
  }

  private static boolean canonicalizeCasts(Statement stat) {
    boolean res = false;
    for (Statement st : stat.getStats()) {
      res |= canonicalizeCasts(st);
    }

    if (stat instanceof BasicBlockStatement) {
      for (Exprent exprent : stat.getExprents()) {
        for (Exprent ex : exprent.getAllExprents(true, true)) {

          // Remove Checkcast(Type, Checkcast(Type, ...)) and turn it just into Checkcast(Type, ...) where both have the same type
          // The extra checkcast causes issues with generic type decompilation
          if (ex instanceof FunctionExprent && ((FunctionExprent)ex).getFuncType() == FunctionExprent.FunctionType.CAST) {
            FunctionExprent func = (FunctionExprent)ex;
            Exprent inner = func.getLstOperands().get(0);
            Exprent cast = func.getLstOperands().get(1);

            if (inner instanceof FunctionExprent && ((FunctionExprent)inner).getFuncType() == FunctionExprent.FunctionType.CAST) {
              FunctionExprent func2 = (FunctionExprent)inner;
              Exprent inner2 = func2.getLstOperands().get(0);
              Exprent cast2 = func2.getLstOperands().get(1);

              if (cast.getExprType().equals(cast2.getExprType())) {
                ex.replaceExprent(inner, inner2);
                ex.addBytecodeOffsets(inner2.bytecode);
                ex.addBytecodeOffsets(inner.bytecode);
                res = true;
              }
            }
          }
        }
      }
    }

    return res;
  }

  public static void markExprOddities(RootStatement root) {
    // We shouldn't have to do this, but turns out getting cast names is not pure. Sigh.
    try (var lock = DecompilerContext.getImportCollector().lock()) {
      markExprOddities(root, root);
    }
  }

  private static void markExprOddities(RootStatement root, Statement stat) {
    for (Statement st : stat.getStats()) {
      markExprOddities(root, st);
    }

    for (Exprent ex : stat.getVarDefinitions()) {
      markExprOddity(root, ex);
    }

    if (stat instanceof BasicBlockStatement) {
      if (stat.isLabeled()) {
        root.addComment("$VF: Made invalid labels!", true);
      }

      for (Exprent ex : stat.getExprents()) {
        markExprOddity(root, ex);
      }
    }
  }

  private static void markExprOddity(RootStatement root, Exprent ex) {
    if (ex instanceof MonitorExprent) {
      root.addComment("$VF: Could not create synchronized statement, marking monitor enters and exits", true);
    }
    if (ex instanceof IfExprent) {
      root.addComment("$VF: Accidentally destroyed if statement, the decompiled code is not correct!", true);
    }

    for (Exprent e : ex.getAllExprents(true, true)) {
      if (e instanceof VarExprent) {
        VarExprent var = (VarExprent)e;
        if (var.isDefinition() && isInvalidTypeName(var.getDefinitionType()) || var.getExprType() == VarType.VARTYPE_UNKNOWN) {
          root.addComment("$VF: Could not properly define all variable types!", true);
        }
      } else if (e instanceof FunctionExprent) {
        FunctionExprent func = (FunctionExprent)e;
        if (func.getFuncType() == FunctionType.CAST && func.doesCast()) {
          List<Exprent> operands = func.getLstOperands();
          if (isInvalidTypeName(operands.get(1).toString())) {
            root.addComment("$VF: Could not properly define all variable types!", true);
          }
        }
      }
    }
  }

  public static String getTypeName(VarType type) {
    return getTypeName(type, true);
  }

  public static String getTypeName(VarType type, boolean getShort) {
    CodeType tp = type.type;
    if (tp.ordinal() <= CodeType.BOOLEAN.ordinal()) {
      return typeNames[tp.ordinal()];
    }
    else if (tp == CodeType.UNKNOWN) {
      return UNKNOWN_TYPE_STRING; // INFO: should not occur
    }
    else if (tp == CodeType.NULL) {
      return NULL_TYPE_STRING; // INFO: should not occur
    }
    else if (tp == CodeType.VOID) {
      return "void";
    }
    else if (tp == CodeType.GENVAR && type.isGeneric()) {
      return type.value;
    }
    else if (tp == CodeType.OBJECT) {
      if (type.isGeneric()) {
        return ((GenericType)type).getCastName();
      }
      String ret = buildJavaClassName(type.value);
      if (getShort) {
        ret = DecompilerContext.getImportCollector().getShortName(ret);
      }

      if (ret == null) {
        ret = UNDEFINED_TYPE_STRING;
      }
      return ret;
    }

    throw new RuntimeException("invalid type: " + tp);
  }

  public static boolean isInvalidTypeName(String name) {
    return UNDEFINED_TYPE_STRING.equals(name) || NULL_TYPE_STRING.equals(name) || UNKNOWN_TYPE_STRING.equals(name);
  }

  public static String getCastTypeName(VarType type) {
    return getCastTypeName(type, true);
  }

  public static String getCastTypeName(VarType type, boolean getShort) {
    StringBuilder s = new StringBuilder(getTypeName(type, getShort));
    TextUtil.append(s, "[]", type.arrayDim);
    return s.toString();
  }

  public static PrimitiveExprsList getExpressionData(VarExprent var) {
    PrimitiveExprsList prlst = new PrimitiveExprsList();
    VarExprent vartmp = new VarExprent(VarExprent.STACK_BASE, var.getExprType(), var.getProcessor());
    vartmp.setStack(true);

    prlst.getLstExprents().add(new AssignmentExprent(vartmp, var.copy(), null));
    prlst.getStack().push(vartmp.copy());
    return prlst;
  }

  /**
   * RTF: chain consecutive assignments with the same simple RHS into a = b = value.
   * Only chains when both LHS are VarExprents and RHS is a simple load (variable,
   * field, or constant). Returns a new list with chained pairs merged.
   */
  private static List<? extends Exprent> chainDupAssignments(List<? extends Exprent> lst) {
    List<Exprent> result = new ArrayList<>(lst);
    for (int i = result.size() - 2; i >= 0; i--) {
      Exprent first = result.get(i);
      Exprent second = result.get(i + 1);

      if (!(first instanceof AssignmentExprent asf) || !(second instanceof AssignmentExprent ass)) continue;
      if (!(asf.getLeft() instanceof VarExprent varA) || !(ass.getLeft() instanceof VarExprent varB)) continue;

      // CRITICAL: only chain when the RHS expressions share a bytecode offset,
      // meaning the value came from the same load (duplicated by dup).
      // Separate load instructions have different offsets.
      Exprent rhsA = asf.getRight();
      Exprent rhsB = ass.getRight();
      if (rhsA.bytecode == null || rhsB.bytecode == null || !rhsA.bytecode.intersects(rhsB.bytecode)) continue;

      // Skip definitions
      if (varA.isDefinition() || varB.isDefinition()) continue;

      // Same RHS, simple expression
      if (!asf.getRight().equals(ass.getRight())) continue;
      Exprent rhs = asf.getRight();
      if (!(rhs instanceof VarExprent) && !(rhs instanceof FieldExprent) && !(rhs instanceof ConstExprent)) continue;

      // Different LHS variables
      if (varA.getIndex() == varB.getIndex()) continue;

      // Chain: second = (first = value) so javac stores first's slot first
      // (matching the original dup; fstore first; fstore second order).
      // javac evaluates chained assignments right-to-left, so the inner
      // assignment (first) gets fstore'd before the outer (second).
      ass.setRight(asf);
      result.set(i, ass);
      result.remove(i + 1);
    }
    return result;
  }

  /**
   * RTF: inline a local variable assignment into the field instance position when the
   * variable was created by a dup that stored a method return value and used it as a
   * field receiver.
   *
   * Pattern matched:
   *   A:  var = invocation()          (assignment with invocation RHS)
   *   ... (intervening statements that do NOT reference var)
   *   B:  var.field = RHS             (field assignment where instance is the same var)
   *
   * Transformed to:
   *   ... (intervening statements preserved)
   *   B': invocation().field = RHS    (A removed, invocation inlined as field instance)
   *
   * Guards:
   *   - A's RHS must be an InvocationExprent
   *   - B is the FIRST reference to the var after A
   *   - B's LHS must be a FieldExprent whose getInstance() is the same var
   *   - The var must NOT appear in B's RHS
   *   - After B, the next reference to the var (if any) must be a reassignment
   *   - All references to this var index in the entire method must be in this list
   *     (prevents unsafe inlining when the var is used in other basic blocks)
   *   - If A is a definition, the definition flag is moved to the next reassignment
   */
  private static List<? extends Exprent> inlineDupFieldReceiver(List<? extends Exprent> lst) {
    List<Exprent> result = new ArrayList<>(lst);

    // Method-wide ref counts are needed for cross-block safety. Cache per var index.
    MethodWrapper method = (MethodWrapper) DecompilerContext.getContextProperty(DecompilerContext.CURRENT_METHOD_WRAPPER);
    if (method == null || method.root == null) return result;

    for (int i = 0; i < result.size() - 1; i++) {
      Exprent first = result.get(i);

      // Statement A must be: var = invocation()
      if (!(first instanceof AssignmentExprent asA)) continue;
      if (!(asA.getLeft() instanceof VarExprent varA)) continue;
      if (!(asA.getRight() instanceof InvocationExprent invocation)) continue;

      int varIndex = varA.getIndex();

      // Find statement B: the FIRST statement after A that references this var.
      // All intervening statements must NOT reference the var.
      int bIdx = -1;
      for (int j = i + 1; j < result.size(); j++) {
        if (containsVarByIndex(result.get(j), varIndex)) {
          bIdx = j;
          break;
        }
      }
      if (bIdx < 0) continue; // var not used after A at all

      Exprent bExpr = result.get(bIdx);

      // Statement B must be: field = RHS, where field's instance is the same var
      if (!(bExpr instanceof AssignmentExprent asB)) continue;
      if (!(asB.getLeft() instanceof FieldExprent fieldB)) continue;
      Exprent fieldInstance = fieldB.getInstance();
      if (!(fieldInstance instanceof VarExprent varInst)) continue;
      if (varInst.getIndex() != varIndex) continue;

      // The var must NOT appear in B's RHS
      if (containsVarByIndex(asB.getRight(), varIndex)) continue;

      // Check statements after B. The next reference to this var must be either
      // nothing or an assignment TO the var (reassignment, meaning the old value is dead).
      boolean safeAfterB = true;
      for (int j = bIdx + 1; j < result.size(); j++) {
        Exprent later = result.get(j);
        if (!containsVarByIndex(later, varIndex)) continue;
        if (later instanceof AssignmentExprent asLater
            && asLater.getLeft() instanceof VarExprent vLater
            && vLater.getIndex() == varIndex
            && !containsVarByIndex(asLater.getRight(), varIndex)) {
          break; // safe: next ref is a reassignment with no var in RHS
        }
        safeAfterB = false;
        break;
      }
      if (!safeAfterB) continue;

      // Method-wide safety: all references to this var must be within this list.
      // If the var is used in other basic blocks, inlining would break them.
      int methodRefs = countVarRefsByIndexInStatement(method.root, varIndex);
      int listRefs = 0;
      for (Exprent expr : result) {
        listRefs += countVarRefsByIndexInExprent(expr, varIndex);
      }
      if (methodRefs != listRefs) continue;

      // If A is a definition and there are later assignments to this var,
      // move the definition flag to the next assignment so the type
      // declaration isn't lost.
      if (varA.isDefinition()) {
        for (int j = bIdx + 1; j < result.size(); j++) {
          Exprent later = result.get(j);
          if (later instanceof AssignmentExprent asLater
              && asLater.getLeft() instanceof VarExprent vLater
              && vLater.getIndex() == varIndex) {
            vLater.setDefinition(true);
            break;
          }
        }
      }

      // All guards passed: inline the invocation as the field's instance
      fieldB.replaceExprent(fieldInstance, invocation);
      result.remove(i);
      i--; // re-check this index since the list shifted
    }
    return result;
  }

  /**
   * Count all references to a variable (by index, ignoring SSA version) across the
   * entire statement tree. Traverses the full method body.
   */
  private static int countVarRefsByIndexInStatement(Statement stat, int varIndex) {
    int count = 0;
    List<Exprent> exprents = stat.getExprents();
    if (exprents != null) {
      for (Exprent expr : exprents) {
        count += countVarRefsByIndexInExprent(expr, varIndex);
      }
    }
    for (Statement child : stat.getStats()) {
      count += countVarRefsByIndexInStatement(child, varIndex);
    }
    return count;
  }

  /**
   * Count all references to a variable (by index, ignoring SSA version) within an
   * expression tree.
   */
  private static int countVarRefsByIndexInExprent(Exprent expr, int varIndex) {
    int count = 0;
    if (expr instanceof VarExprent ve && ve.getIndex() == varIndex) {
      count++;
    }
    for (Exprent child : expr.getAllExprents(true)) {
      if (child instanceof VarExprent ve && ve.getIndex() == varIndex) {
        count++;
      }
    }
    return count;
  }

  /**
   * Check if an expression tree contains any VarExprent with the given variable index,
   * regardless of SSA version.
   */
  private static boolean containsVarByIndex(Exprent expr, int varIndex) {
    if (expr instanceof VarExprent ve && ve.getIndex() == varIndex) {
      return true;
    }
    for (Exprent child : expr.getAllExprents(true)) {
      if (child instanceof VarExprent ve && ve.getIndex() == varIndex) {
        return true;
      }
    }
    return false;
  }

  /**
   * RTF: replace duplicate field reads in if-conditions with the variable that
   * was assigned from the same field in the head block.
   *
   * Detects:
   *   first block: [..., var = obj.field]
   *   condition:   ... obj.field ... var ...
   *
   * The original bytecode used DUP to share a single field read for both the
   * variable assignment and the condition comparison. Vineflower splits this into
   * two separate field reads. This pass replaces the duplicate field read in the
   * condition with the variable, restoring the original instruction count.
   *
   * Walks the entire statement tree recursively.
   */
  public static boolean replaceDupFieldReadsInConditions(Statement stat) {
    boolean changed = false;

    // Process children first (bottom-up)
    for (Statement child : new ArrayList<>(stat.getStats())) {
      changed |= replaceDupFieldReadsInConditions(child);
    }

    if (!(stat instanceof IfStatement ifStat)) {
      return changed;
    }

    Statement head = ifStat.getFirst();
    List<Exprent> headExprents = head.getExprents();
    if (headExprents == null || headExprents.isEmpty()) {
      return changed;
    }

    Exprent condExprent = ifStat.getHeadexprentList().get(0);
    if (condExprent == null) {
      return changed;
    }

    // Check each assignment in the head block (iterate from last to first,
    // since later assignments are closer to the condition)
    for (int i = headExprents.size() - 1; i >= 0; i--) {
      Exprent expr = headExprents.get(i);
      if (!(expr instanceof AssignmentExprent asn)) continue;
      if (!(asn.getLeft() instanceof VarExprent varExpr)) continue;
      if (!(asn.getRight() instanceof FieldExprent fieldExpr)) continue;

      // The field must be an instance field (not static) to match the DUP pattern
      // Static fields don't use DUP in this pattern
      if (fieldExpr.isStatic()) continue;

      // Verify the variable is used somewhere in the condition
      // (otherwise there's no DUP pattern to reconstruct)
      int varIdx = varExpr.getIndex();
      if (!containsVarByIndex(condExprent, varIdx)) continue;

      // Check that no statements between this assignment and the condition
      // could modify the field (conservative: no other exprents after this one
      // that write to the same field or the same object)
      boolean safeToReplace = true;
      for (int j = i + 1; j < headExprents.size(); j++) {
        Exprent later = headExprents.get(j);
        // If any later exprent references the same field or could have side effects,
        // bail out. For safety, check if the later exprent contains a field write
        // to the same field or an invocation.
        if (containsFieldWrite(later, fieldExpr) || containsInvocation(later)) {
          safeToReplace = false;
          break;
        }
      }
      if (!safeToReplace) continue;

      // Find and replace the matching field expression in the condition.
      // We need to find the exact FieldExprent instance that equals our fieldExpr.
      if (replaceFieldWithVarInTree(condExprent, fieldExpr, varExpr)) {
        changed = true;
      }
    }

    return changed;
  }

  /**
   * Recursively find a FieldExprent in the expression tree that equals the target
   * field expression, and replace it with a copy of the variable expression.
   * Returns true if a replacement was made.
   */
  private static boolean replaceFieldWithVarInTree(Exprent root, FieldExprent targetField, VarExprent varExpr) {
    // Check direct children
    for (Exprent child : root.getAllExprents()) {
      if (child instanceof FieldExprent fe && fe.equals(targetField) && fe != targetField) {
        // Create a copy of the var expression for replacement.
        // Clear the definition flag since this is a use, not a declaration.
        VarExprent replacement = (VarExprent) varExpr.copy();
        replacement.setDefinition(false);
        replacement.addBytecodeOffsets(fe.bytecode);
        root.replaceExprent(child, replacement);
        return true;
      }
      // Recurse into children
      if (replaceFieldWithVarInTree(child, targetField, varExpr)) {
        return true;
      }
    }
    return false;
  }

  /**
   * Check if an expression tree contains a field write (assignment) to the same
   * field as the target.
   */
  private static boolean containsFieldWrite(Exprent expr, FieldExprent targetField) {
    if (expr instanceof AssignmentExprent asn && asn.getLeft() instanceof FieldExprent fe) {
      if (fe.getName().equals(targetField.getName()) && fe.getClassname().equals(targetField.getClassname())) {
        return true;
      }
    }
    for (Exprent child : expr.getAllExprents(true)) {
      if (child instanceof AssignmentExprent asn && asn.getLeft() instanceof FieldExprent fe) {
        if (fe.getName().equals(targetField.getName()) && fe.getClassname().equals(targetField.getClassname())) {
          return true;
        }
      }
    }
    return false;
  }

  /**
   * Check if an expression tree contains any method invocation.
   */
  private static boolean containsInvocation(Exprent expr) {
    if (expr instanceof InvocationExprent) return true;
    for (Exprent child : expr.getAllExprents(true)) {
      if (child instanceof InvocationExprent) return true;
    }
    return false;
  }

  public static boolean endsWithSemicolon(Exprent expr) {
    return !(expr instanceof SwitchHeadExprent ||
             expr instanceof MonitorExprent ||
             expr instanceof IfExprent ||
             (expr instanceof VarExprent && ((VarExprent)expr).isClassDef()));
  }

  private static void addDeletedGotoInstructionMapping(Statement stat, TextBuffer buffer) {
    if (stat instanceof BasicBlockStatement) {
      BasicBlock block = ((BasicBlockStatement)stat).getBlock();
      List<Integer> offsets = block.getInstrOldOffsets();
      if (!offsets.isEmpty() &&
          offsets.size() > block.getSeq().length()) { // some instructions have been deleted, but we still have offsets
        buffer.addBytecodeMapping(offsets.get(offsets.size() - 1)); // add the last offset
      }
    }
  }

  public static TextBuffer jmpWrapper(Statement stat, int indent, boolean semicolon) {
    TextBuffer buf = stat.toJava(indent);

    List<StatEdge> lstSuccs = stat.getSuccessorEdges(Statement.STATEDGE_DIRECT_ALL);
    if (lstSuccs.size() == 1) {
      StatEdge edge = lstSuccs.get(0);
      if (edge.getType() != StatEdge.TYPE_REGULAR && edge.explicit && !(edge.getDestination() instanceof DummyExitStatement)) {
        buf.appendIndent(indent);

        switch (edge.getType()) {
          case StatEdge.TYPE_BREAK:
            addDeletedGotoInstructionMapping(stat, buf);
            buf.append("break");
            break;
          case StatEdge.TYPE_CONTINUE:
            addDeletedGotoInstructionMapping(stat, buf);
            buf.append("continue");
        }

        if (edge.labeled) {
          buf.append(" label").append(edge.closure.id);
        }
        buf.append(";").appendLineSeparator();
      }
    }

    if (buf.length() == 0 && semicolon) {
      buf.appendIndent(indent).append(";").appendLineSeparator();
    }

    return buf;
  }

  public static String buildJavaClassName(String name) {
    String res = name.replace('/', '.');

    if (res.contains("$")) { // attempt to invoke foreign member
      // classes correctly
      StructClass cl = DecompilerContext.getStructContext().getClass(name);
      if (cl == null || !cl.isOwn()) {
        res = res.replace('$', '.');
      }
    }

    return res;
  }

  public static TextBuffer listToJava(List<? extends Exprent> lst, int indent) {
    if (lst == null || lst.isEmpty()) {
      return new TextBuffer();
    }

    TextBuffer buf = new TextBuffer();
    lst = Exprent.sortIndexed(lst);

    // RTF: chain consecutive assignments that share a bytecode offset (from dup).
    if (DecompilerContext.isRoundtripFidelity() && lst.size() >= 2) {
      lst = chainDupAssignments(lst);
      lst = inlineDupFieldReceiver(lst);
    }

    for (Exprent expr : lst) {
      if (buf.length() > 0 && expr instanceof VarExprent && ((VarExprent)expr).isClassDef()) {
        // separates local class definition from previous statements
        buf.appendLineSeparator();
      }

      expr.getInferredExprType(null);

      // RTF: mark statement-level expressions so toJava() can skip casts
      // that would create "not a statement" errors
      if (DecompilerContext.isRoundtripFidelity()) {
        expr.rtfStatementLevel = true;
      }

      TextBuffer content = expr.toJava(indent);

      if (content.length() > 0) {
        if (!(expr instanceof VarExprent) || !((VarExprent)expr).isClassDef()) {
          buf.appendIndent(indent);
        }
        buf.append(content);
        if (expr instanceof MonitorExprent && ((MonitorExprent)expr).getMonType() == MonitorExprent.Type.ENTER) {
          buf.append("{} // $VF: monitorenter "); // empty synchronized block
        }
        if (endsWithSemicolon(expr)) {
          buf.append(";");
        }
        buf.appendLineSeparator();
      }
    }

    return buf;
  }

  public static ConstExprent getDefaultArrayValue(VarType arrType) {
    ConstExprent defaultVal;
    if (arrType.type == CodeType.OBJECT || arrType.arrayDim > 0) {
      defaultVal = new ConstExprent(VarType.VARTYPE_NULL, null, null);
    }
    else if (arrType.type == CodeType.FLOAT) {
      defaultVal = new ConstExprent(VarType.VARTYPE_FLOAT, 0f, null);
    }
    else if (arrType.type == CodeType.LONG) {
      defaultVal = new ConstExprent(VarType.VARTYPE_LONG, 0L, null);
    }
    else if (arrType.type == CodeType.DOUBLE) {
      defaultVal = new ConstExprent(VarType.VARTYPE_DOUBLE, 0d, null);
    }
    else { // integer types
      defaultVal = new ConstExprent(0, true, null);
    }
    return defaultVal;
  }

  public static boolean getCastedExprent(Exprent exprent,
                                         VarType leftType,
                                         TextBuffer buffer,
                                         int indent,
                                         boolean castNull) {
    return getCastedExprent(exprent, leftType, buffer, indent, castNull ? NullCastType.CAST : NullCastType.DONT_CAST, false, false, false);
  }

  public static boolean getCastedExprent(Exprent exprent,
                                         VarType leftType,
                                         TextBuffer buffer,
                                         int indent,
                                         NullCastType castNull,
                                         boolean castAlways,
                                         boolean castNarrowing,
                                         boolean unbox) {

    if (unbox) {
      // "unbox" invocation parameters, e.g. 'byteSet.add((byte)123)' or 'new ShortContainer((short)813)'
      if (exprent instanceof InvocationExprent) {
        InvocationExprent invocationExprent = (InvocationExprent) exprent;
        if (invocationExprent.isBoxingCall() && !invocationExprent.shouldForceBoxing()) {
          exprent = invocationExprent.getLstParameters().get(0);
          CodeType paramType = invocationExprent.getDescriptor().params[0].type;
          if (exprent instanceof ConstExprent && ((ConstExprent) exprent).getConstType().type != paramType) {
            leftType = new VarType(paramType);
          }
        }
      }
    }

    VarType rightType = exprent.getInferredExprType(leftType);
    exprent = narrowGenericCastType(exprent, leftType);

    boolean doCast = (!leftType.isSuperset(rightType) && (rightType.equals(VarType.VARTYPE_OBJECT) || leftType.type != CodeType.OBJECT));
    boolean doCastNull = (castNull.cast && rightType.type == CodeType.NULL && !UNDEFINED_TYPE_STRING.equals(getTypeName(leftType)));
    boolean doCastNarrowing = (castNarrowing && isIntConstant(exprent) && isNarrowedIntType(leftType));
    boolean doCastGenerics = doGenericTypesCast(exprent, leftType, rightType);

    // RTF: force narrowing cast when LHS is byte/short/char and RHS is an arithmetic operation.
    // Java promotes byte/short/char to int in arithmetic, so the result needs an explicit cast back.
    // The decompiler's type system may report the RHS as byte (matching LHS), but Java requires the cast.
    boolean doCastRtfNarrowing = false;
    if (DecompilerContext.isRoundtripFidelity() && exprent instanceof FunctionExprent) {
      FunctionExprent func = (FunctionExprent) exprent;
      FunctionType ft = func.getFuncType();
      boolean isArithmetic = ft == FunctionType.ADD || ft == FunctionType.SUB
          || ft == FunctionType.MUL || ft == FunctionType.DIV || ft == FunctionType.REM
          || ft == FunctionType.AND || ft == FunctionType.OR || ft == FunctionType.XOR
          || ft == FunctionType.SHL || ft == FunctionType.SHR || ft == FunctionType.USHR;
      boolean isNarrowLhs = leftType.type == CodeType.BYTE || leftType.type == CodeType.SHORT
          || leftType.type == CodeType.CHAR || leftType.type == CodeType.BYTECHAR
          || leftType.type == CodeType.SHORTCHAR;
      if (isArithmetic && isNarrowLhs) {
        doCastRtfNarrowing = true;
      }
    }

    // RTF: when leftType is a GENVAR (T, V, R) or a concrete type (ArrayList)
    // but the expression's actual type (from descriptor/erased type) is Object,
    // force a cast. getInferredExprType resolves the type variable or matches the
    // upper bound, hiding the Object→T or Object→ArrayList gap javac would reject.
    boolean doCastRtfGenvar = false;
    if (DecompilerContext.isRoundtripFidelity()) {
      VarType actualType = exprent.getExprType();
      if (actualType.type == CodeType.OBJECT && "java/lang/Object".equals(actualType.value)) {
        if (leftType.type == CodeType.GENVAR) {
          doCastRtfGenvar = true;
        } else if (leftType.type == CodeType.OBJECT && !"java/lang/Object".equals(leftType.value)
            && !doCast && exprent instanceof VarExprent) {
          // Concrete type LHS with Object actual (from erased method param)
          // Only for VarExprent to avoid false positives on complex expressions
          doCastRtfGenvar = true;
        }
      }
    }
    // RTF: generic invariance — same base class but different type args.
    // E.g., Pool<IPooledObject> param receiving Pool<PO> argument.
    // Triggers when both are GenericType with different args, OR when leftType
    // is raw but rightType is GenericType with GENVAR args (the rendered output
    // will have generic types from signatures causing invariance errors).
    boolean doCastRtfInvariance = false;
    if (DecompilerContext.isRoundtripFidelity() && !doCast && !doCastRtfGenvar) {
      if (leftType instanceof GenericType && rightType instanceof GenericType
          && leftType.value != null && leftType.value.equals(rightType.value)) {
        // VarType.equals ignores generic arguments, so compare them explicitly
        GenericType lg = (GenericType) leftType;
        GenericType rg = (GenericType) rightType;
        if (!lg.getArguments().equals(rg.getArguments())) {
          // Only for GENVAR arguments from the CURRENT class/method scope
          // Don't trigger for concrete→concrete or out-of-scope GENVARs
          boolean rightHasLocalGenvar = false;
          for (VarType arg : rg.getArguments()) {
            if (arg.type == CodeType.GENVAR) {
              // Verify GENVAR is in current scope
              boolean inScope = false;
              org.jetbrains.java.decompiler.main.rels.MethodWrapper mw =
                  DecompilerContext.getContextProperty(DecompilerContext.CURRENT_METHOD_WRAPPER);
              if (mw != null && mw.methodStruct.getSignature() != null) {
                for (String tp : mw.methodStruct.getSignature().typeParameters) {
                  if (arg.value.equals(tp)) { inScope = true; break; }
                }
              }
              if (!inScope) {
                org.jetbrains.java.decompiler.main.ClassesProcessor.ClassNode cls =
                    DecompilerContext.getContextProperty(DecompilerContext.CURRENT_CLASS_NODE);
                while (cls != null && !inScope) {
                  if (cls.classStruct.getSignature() != null) {
                    for (String tp : cls.classStruct.getSignature().fparameters) {
                      if (arg.value.equals(tp)) { inScope = true; break; }
                    }
                  }
                  cls = cls.parent;
                }
              }
              if (inScope) { rightHasLocalGenvar = true; break; }
            }
          }
          if (rightHasLocalGenvar) {
            doCastRtfInvariance = true;
          }
        }
      }
      // When leftType is raw but rightType is GenericType with GENVAR args
      // (from class signature), the rendered code will show the generic types
      // and javac will reject due to invariance
      if (!doCastRtfInvariance && !(leftType instanceof GenericType)
          && rightType instanceof GenericType
          && leftType.value != null && leftType.value.equals(rightType.value)
          && !leftType.equals(rightType)) {
        // Check if rightType has GENVAR arguments
        boolean hasGenvar = false;
        for (VarType arg : ((GenericType)rightType).getArguments()) {
          if (arg.type == CodeType.GENVAR) { hasGenvar = true; break; }
        }
        if (hasGenvar) {
          doCastRtfInvariance = true;
        }
      }
    }
    if (doCastRtfInvariance) {
      // Use raw type (strip generic args) for the cast
      leftType = new VarType(CodeType.OBJECT, leftType.arrayDim, leftType.value);
    }

    boolean cast = castAlways || doCast || doCastNull || doCastNarrowing || doCastGenerics || doCastRtfNarrowing || doCastRtfGenvar || doCastRtfInvariance;

    // RTF: validate GENVAR cast targets are in scope. If casting to a type variable
    // from a different class (e.g., ReturnValueContainer's T, Function's T) that's
    // not declared by the current method, class, or enclosing classes, skip the cast.
    if (cast && DecompilerContext.isRoundtripFidelity() && leftType.type == CodeType.GENVAR) {
      boolean inScope = false;
      org.jetbrains.java.decompiler.main.rels.MethodWrapper mw =
          DecompilerContext.getContextProperty(DecompilerContext.CURRENT_METHOD_WRAPPER);
      if (mw != null && mw.methodStruct.getSignature() != null) {
        for (String tp : mw.methodStruct.getSignature().typeParameters) {
          if (leftType.value.equals(tp)) { inScope = true; break; }
        }
      }
      if (!inScope) {
        // Walk up the class hierarchy (current class + enclosing classes)
        org.jetbrains.java.decompiler.main.ClassesProcessor.ClassNode cls =
            DecompilerContext.getContextProperty(DecompilerContext.CURRENT_CLASS_NODE);
        while (cls != null && !inScope) {
          if (cls.classStruct.getSignature() != null) {
            for (String tp : cls.classStruct.getSignature().fparameters) {
              if (leftType.value.equals(tp)) { inScope = true; break; }
            }
          }
          cls = cls.parent;
        }
      }
      if (!inScope) {
        cast = false;
      }
    }

    if (castNull == NullCastType.DONT_CAST_AT_ALL && rightType.type == CodeType.NULL) {
      cast = castAlways;
    }

    boolean castLambda = !cast && exprent instanceof NewExprent && !leftType.equals(rightType) &&
                          lambdaNeedsCast(leftType, (NewExprent)exprent);

    boolean quote = cast && exprent.getPrecedence() >= FunctionType.CAST.precedence;

    // cast instead to 'byte' / 'short' when int constant is used as a value for 'Byte' / 'Short'
    if (castNarrowing && exprent instanceof ConstExprent && !((ConstExprent) exprent).isNull()) {
      if (leftType.equals(VarType.VARTYPE_BYTE_OBJ)) {
        leftType = VarType.VARTYPE_BYTE;
      }
      else if (leftType.equals(VarType.VARTYPE_SHORT_OBJ)) {
        leftType = VarType.VARTYPE_SHORT;
      }
    }

    if (cast) {
      // RTF: Java does not allow (boolean)intExpr. Replace with intExpr != 0.
      if (DecompilerContext.isRoundtripFidelity()
          && leftType.equals(VarType.VARTYPE_BOOLEAN)
          && rightType.typeFamily == TypeFamily.INTEGER) {
        if (exprent instanceof ConstExprent) {
          // Constants 0/1: suppress cast, emit bare value (int var = 1 is valid)
          cast = false;
        } else {
          // Non-constants: emit expr != 0 instead of (boolean)expr
          buffer.append(exprent.toJava(indent)).append(" != 0");
          return true;
        }
      }
      if (cast) {
        buffer.append('(').appendCastTypeName(leftType).append(')');
      }
    }

    if (castLambda) {
      buffer.append('(').appendCastTypeName(rightType).append(')');
    }

    if (quote) {
      buffer.append('(');
    }

    if (exprent instanceof ConstExprent) {
      ((ConstExprent) exprent).adjustConstType(leftType);
    }

    if (cast) {
      // Don't cast vararg array creation! Force regular array creation instead
      if (exprent instanceof NewExprent && ((NewExprent)exprent).isVarArgParam()) {
        ((NewExprent) exprent).setVarArgParam(false);
      }
    }

    buffer.append(exprent.toJava(indent));

    if (quote) {
      buffer.append(')');
    }

    return cast;
  }

  public enum NullCastType {
    CAST(true), // old boolean true
    DONT_CAST(false), // old boolean false
    DONT_CAST_AT_ALL(false); // old boolean false and don't cast

    private final boolean cast;

    NullCastType(boolean cast) {
      this.cast = cast;
    }
  }

  // (Obj)expr; -> (Obj<T>)expr;
  public static Exprent narrowGenericCastType(Exprent expr, VarType type) {
    if (type.isGeneric() && expr instanceof FunctionExprent && ((FunctionExprent)expr).getFuncType() == FunctionType.CAST) {
      FunctionExprent func = (FunctionExprent) expr;
      VarType funcType = func.getExprType();

      GenericType genType = (GenericType) type;
      if (funcType.value.equals(type.value) && !genType.getArguments().isEmpty()) {
        // Trying to cast to a generic type but the cast isn't generic- invalid!
        if (!funcType.isGeneric()) {
          ConstExprent cast = ((ConstExprent) func.getLstOperands().get(1));
          cast.setConstType(type);
        } else if (genType.equalsExact(funcType) && !func.doesCast()) {
          func.setNeedsCast(true);
        }
      }
    }

    return expr;
  }

  // Checks if two generic types should cast based on their type parameters.
  // If both the left and the right types are generics, compare the type parameters based on a set of rules to see if
  // the types are compatible. If a matching rule is identified, return and inform the type processor that the types
  // should cast.
  private static boolean doGenericTypesCast(Exprent ex, VarType left, VarType right) {
    Map<VarType, List<VarType>> named = ex.getNamedGenerics();
    if (left == null || right == null) {
      return false;
    }

    if (left.isGeneric() && right.isGeneric()) {
      if (shouldGenericTypesCast(named, left, right)) {
        return true;
      }

      GenericType leftGeneric = (GenericType) left;
      GenericType rightGeneric = (GenericType) right;

      if (leftGeneric.getArguments().size() != rightGeneric.getArguments().size()) {
        return false;
      }

      for (int i = 0; i < leftGeneric.getArguments().size(); i++) {
        VarType leftType = leftGeneric.getArguments().get(i);
        VarType rightType = rightGeneric.getArguments().get(i);
        if (rightType == null && leftType != null) {
          return true;
        }

        if (leftType != null) {
          if (shouldGenericTypesCast(named, leftType, rightType)) {
            return true;
          }
        }
      }
    }

    return false;
  }

  private static boolean shouldGenericTypesCast(Map<VarType, List<VarType>> named, VarType leftType, VarType rightType) {
    if (leftType.isGeneric()) {
      GenericType genLeft = (GenericType) leftType;
      if (rightType.isGeneric()) {
        GenericType genRight = (GenericType) rightType;

        if (leftType.isSuperset(rightType)) {
          // Casting Clazz<?> to Clazz<T> or Clazz<Concrete>
          if ((genLeft.getWildcard() == GenericType.WILDCARD_NO || genLeft.getWildcard() == GenericType.WILDCARD_EXTENDS) &&
            genRight.getWildcard() == GenericType.WILDCARD_SUPER) {

            boolean ok = true;
            if (genLeft.getWildcard() == GenericType.WILDCARD_EXTENDS) {
              // Equals, ignoring wildcards
              if (!genLeft.getArguments().isEmpty() && !genRight.getArguments().isEmpty() &&
                leftType.equals(rightType)) {
                ok = false;
              }
            }

            if (ok) {
              return true;
            }
          }
        } else {
          if (genLeft.getWildcard() == GenericType.WILDCARD_EXTENDS && genRight.getWildcard() == GenericType.WILDCARD_SUPER) {
            return true;
          }
          // Trying to cast two independent generics to each other? Check if they're both the base generic type (i.e. Object)
          // and force a cast if so.
          if (leftType.type == CodeType.GENVAR && rightType.type == CodeType.GENVAR
            && genLeft.getWildcard() == GenericType.WILDCARD_NO && genLeft.getWildcard() == GenericType.WILDCARD_NO) {

            if (named.containsKey(leftType) && named.containsKey(rightType) && named.get(leftType).contains(VarType.VARTYPE_OBJECT) && named.get(rightType).contains(VarType.VARTYPE_OBJECT)) {
              return true;
            }
          }
        }

        if ((genLeft.getWildcard() == GenericType.WILDCARD_NO || genLeft.getWildcard() == GenericType.WILDCARD_SUPER) &&
          genRight.getWildcard() == GenericType.WILDCARD_EXTENDS) {
          return true;
        }

        // Recurse on the type
        // Notably, *only* recurse if the current wildcard types are the same- otherwise we may run into incorrect casting behavior
        if (genLeft.getArguments().size() != genRight.getArguments().size()) {
          return false;
        }

        if (genLeft.getWildcard() == genRight.getWildcard()) {
          for (int i = 0; i < genLeft.getArguments().size(); i++) {
            VarType lt = genLeft.getArguments().get(i);
            VarType rt = genRight.getArguments().get(i);
            // Subset of Type<?> -> Type<T> check: Only check for genvars. If T is concrete, then don't force casting.
            if (rt == null && lt != null && lt.type == CodeType.GENVAR) {
              return true;
            }

            if (lt != null && rt != null) {
              if (shouldGenericTypesCast(named, lt, rt)) {
                return true;
              }
            }
          }
        }
      } else {
        // Right is not generic
        // Check for casting a concrete rightType to a specific left generic
        // e.g. (List<T>)list where 'list' is List<Object>
        if (genLeft.getWildcard() == GenericType.WILDCARD_NO && genLeft.getArguments().isEmpty()) {
          return true;
        }
      }
    }

    return false;
  }

  private static boolean isIntConstant(Exprent exprent) {
    if (exprent instanceof ConstExprent) {
      switch (((ConstExprent)exprent).getConstType().type) {
        case BYTE:
        case BYTECHAR:
        case SHORT:
        case SHORTCHAR:
        case INT:
          return true;
      }
    }

    return false;
  }

  private static boolean isNarrowedIntType(VarType type) {
    return VarType.VARTYPE_INT.isStrictSuperset(type) ||
           type.equals(VarType.VARTYPE_BYTE_OBJ) || type.equals(VarType.VARTYPE_SHORT_OBJ);
  }

  private static boolean lambdaNeedsCast(VarType left, NewExprent exprent) {
    if (exprent.isLambda() && !exprent.isMethodReference()) {
      StructClass cls = DecompilerContext.getStructContext().getClass(left.value);
      return cls == null || cls.getMethod(exprent.getLambdaMethodKey()) == null;
    }
    return false;
  }
}
