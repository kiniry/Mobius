package b2bpl.bytecode;

import org.objectweb.asm.Type;

import b2bpl.bytecode.instructions.AALoadInstruction;
import b2bpl.bytecode.instructions.AAStoreInstruction;
import b2bpl.bytecode.instructions.AConstNullInstruction;
import b2bpl.bytecode.instructions.ALoadInstruction;
import b2bpl.bytecode.instructions.ANewArrayInstruction;
import b2bpl.bytecode.instructions.AReturnInstruction;
import b2bpl.bytecode.instructions.AStoreInstruction;
import b2bpl.bytecode.instructions.AThrowInstruction;
import b2bpl.bytecode.instructions.ArrayLengthInstruction;
import b2bpl.bytecode.instructions.CheckCastInstruction;
import b2bpl.bytecode.instructions.Dup2Instruction;
import b2bpl.bytecode.instructions.Dup2X1Instruction;
import b2bpl.bytecode.instructions.Dup2X2Instruction;
import b2bpl.bytecode.instructions.DupInstruction;
import b2bpl.bytecode.instructions.DupX1Instruction;
import b2bpl.bytecode.instructions.DupX2Instruction;
import b2bpl.bytecode.instructions.GetFieldInstruction;
import b2bpl.bytecode.instructions.GetStaticInstruction;
import b2bpl.bytecode.instructions.GotoInstruction;
import b2bpl.bytecode.instructions.IBinArithInstruction;
import b2bpl.bytecode.instructions.IBitwiseInstruction;
import b2bpl.bytecode.instructions.IIncInstruction;
import b2bpl.bytecode.instructions.ILoadInstruction;
import b2bpl.bytecode.instructions.INegInstruction;
import b2bpl.bytecode.instructions.IReturnInstruction;
import b2bpl.bytecode.instructions.IStoreInstruction;
import b2bpl.bytecode.instructions.IfACmpInstruction;
import b2bpl.bytecode.instructions.IfICmpInstruction;
import b2bpl.bytecode.instructions.IfInstruction;
import b2bpl.bytecode.instructions.IfNonNullInstruction;
import b2bpl.bytecode.instructions.IfNullInstruction;
import b2bpl.bytecode.instructions.InstanceOfInstruction;
import b2bpl.bytecode.instructions.Instruction;
import b2bpl.bytecode.instructions.InvokeInterfaceInstruction;
import b2bpl.bytecode.instructions.InvokeSpecialInstruction;
import b2bpl.bytecode.instructions.InvokeStaticInstruction;
import b2bpl.bytecode.instructions.InvokeVirtualInstruction;
import b2bpl.bytecode.instructions.LBinArithInstruction;
import b2bpl.bytecode.instructions.LBitwiseInstruction;
import b2bpl.bytecode.instructions.LCmpInstruction;
import b2bpl.bytecode.instructions.LLoadInstruction;
import b2bpl.bytecode.instructions.LNegInstruction;
import b2bpl.bytecode.instructions.LReturnInstruction;
import b2bpl.bytecode.instructions.LStoreInstruction;
import b2bpl.bytecode.instructions.LdcInstruction;
import b2bpl.bytecode.instructions.LookupSwitchInstruction;
import b2bpl.bytecode.instructions.MultiANewArrayInstruction;
import b2bpl.bytecode.instructions.NewArrayInstruction;
import b2bpl.bytecode.instructions.NewInstruction;
import b2bpl.bytecode.instructions.NopInstruction;
import b2bpl.bytecode.instructions.Pop2Instruction;
import b2bpl.bytecode.instructions.PopInstruction;
import b2bpl.bytecode.instructions.PutFieldInstruction;
import b2bpl.bytecode.instructions.PutStaticInstruction;
import b2bpl.bytecode.instructions.ReturnInstruction;
import b2bpl.bytecode.instructions.SwapInstruction;
import b2bpl.bytecode.instructions.TableSwitchInstruction;
import b2bpl.bytecode.instructions.VALoadInstruction;
import b2bpl.bytecode.instructions.VAStoreInstruction;
import b2bpl.bytecode.instructions.VCastInstruction;
import b2bpl.bytecode.instructions.VConstantInstruction;


public class InstructionFactory {

  public static Instruction fromInsn(int opcode)
      throws UnsupportedInstructionException {
    switch (opcode) {
      case IOpCodes.NOP:
        return NopInstruction.NOP;
      case IOpCodes.ICONST_M1:
        return VConstantInstruction.ICONST_M1;
      case IOpCodes.ICONST_0:
        return VConstantInstruction.ICONST_0;
      case IOpCodes.ICONST_1:
        return VConstantInstruction.ICONST_1;
      case IOpCodes.ICONST_2:
        return VConstantInstruction.ICONST_2;
      case IOpCodes.ICONST_3:
        return VConstantInstruction.ICONST_3;
      case IOpCodes.ICONST_4:
        return VConstantInstruction.ICONST_4;
      case IOpCodes.ICONST_5:
        return VConstantInstruction.ICONST_5;
      case IOpCodes.LCONST_0:
        return VConstantInstruction.LCONST_0;
      case IOpCodes.LCONST_1:
        return VConstantInstruction.LCONST_1;
      case IOpCodes.ACONST_NULL:
        return AConstNullInstruction.ACONST_NULL;
      case IOpCodes.IALOAD:
        return VALoadInstruction.IALOAD;
      case IOpCodes.SALOAD:
        return VALoadInstruction.SALOAD;
      case IOpCodes.BALOAD:
        return VALoadInstruction.BALOAD;
      case IOpCodes.CALOAD:
        return VALoadInstruction.CALOAD;
      case IOpCodes.LALOAD:
        return VALoadInstruction.LALOAD;
      case IOpCodes.AALOAD:
        return AALoadInstruction.AALOAD;
      case IOpCodes.IASTORE:
        return VAStoreInstruction.IASTORE;
      case IOpCodes.SASTORE:
        return VAStoreInstruction.SASTORE;
      case IOpCodes.BASTORE:
        return VAStoreInstruction.BASTORE;
      case IOpCodes.CASTORE:
        return VAStoreInstruction.CASTORE;
      case IOpCodes.LASTORE:
        return VAStoreInstruction.LASTORE;
      case IOpCodes.AASTORE:
        return AAStoreInstruction.AASTORE;
      case IOpCodes.ARRAYLENGTH:
        return ArrayLengthInstruction.ARRAYLENGTH;
      case IOpCodes.IADD:
        return IBinArithInstruction.IADD;
      case IOpCodes.ISUB:
        return IBinArithInstruction.ISUB;
      case IOpCodes.IMUL:
        return IBinArithInstruction.IMUL;
      case IOpCodes.IDIV:
        return IBinArithInstruction.IDIV;
      case IOpCodes.IREM:
        return IBinArithInstruction.IREM;
      case IOpCodes.LADD:
        return LBinArithInstruction.LADD;
      case IOpCodes.LSUB:
        return LBinArithInstruction.LSUB;
      case IOpCodes.LMUL:
        return LBinArithInstruction.LMUL;
      case IOpCodes.LDIV:
        return LBinArithInstruction.LDIV;
      case IOpCodes.LREM:
        return LBinArithInstruction.LREM;
      case IOpCodes.INEG:
        return INegInstruction.INEG;
      case IOpCodes.LNEG:
        return LNegInstruction.LNEG;
      case IOpCodes.ISHL:
        return IBitwiseInstruction.ISHL;
      case IOpCodes.ISHR:
        return IBitwiseInstruction.ISHR;
      case IOpCodes.IUSHR:
        return IBitwiseInstruction.IUSHR;
      case IOpCodes.IAND:
        return IBitwiseInstruction.IAND;
      case IOpCodes.IOR:
        return IBitwiseInstruction.IOR;
      case IOpCodes.IXOR:
        return IBitwiseInstruction.IXOR;
      case IOpCodes.LSHL:
        return LBitwiseInstruction.LSHL;
      case IOpCodes.LSHR:
        return LBitwiseInstruction.LSHR;
      case IOpCodes.LUSHR:
        return LBitwiseInstruction.LUSHR;
      case IOpCodes.LAND:
        return LBitwiseInstruction.LAND;
      case IOpCodes.LOR:
        return LBitwiseInstruction.LOR;
      case IOpCodes.LXOR:
        return LBitwiseInstruction.LXOR;
      case IOpCodes.I2S:
        return VCastInstruction.I2S;
      case IOpCodes.I2B:
        return VCastInstruction.I2B;
      case IOpCodes.I2C:
        return VCastInstruction.I2C;
      case IOpCodes.I2L:
        return VCastInstruction.I2L;
      case IOpCodes.L2I:
        return VCastInstruction.L2I;
      case IOpCodes.LCMP:
        return LCmpInstruction.LCMP;
      case IOpCodes.RETURN:
        return ReturnInstruction.RETURN;
      case IOpCodes.IRETURN:
        return IReturnInstruction.IRETURN;
      case IOpCodes.LRETURN:
        return LReturnInstruction.LRETURN;
      case IOpCodes.ARETURN:
        return AReturnInstruction.ARETURN;
      case IOpCodes.ATHROW:
        return AThrowInstruction.ATHROW;
      case IOpCodes.POP:
        return PopInstruction.POP;
      case IOpCodes.POP2:
        return Pop2Instruction.POP2;
      case IOpCodes.SWAP:
        return SwapInstruction.SWAP;
      case IOpCodes.DUP:
        return DupInstruction.DUP;
      case IOpCodes.DUP2:
        return Dup2Instruction.DUP2;
      case IOpCodes.DUP_X1:
        return DupX1Instruction.DUP_X1;
      case IOpCodes.DUP_X2:
        return DupX2Instruction.DUP_X2;
      case IOpCodes.DUP2_X1:
        return Dup2X1Instruction.DUP2_X1;
      case IOpCodes.DUP2_X2:
        return Dup2X2Instruction.DUP2_X2;
      default:
        throw new UnsupportedInstructionException(opcode);
    }
  }

  public static Instruction fromIntInsn(int opcode, int operand)
      throws UnsupportedInstructionException {
    switch (opcode) {
      case IOpCodes.BIPUSH:
      case IOpCodes.SIPUSH:
        return VConstantInstruction.createIConstant(operand);
      case IOpCodes.NEWARRAY:
        switch (operand) {
          case IOpCodes.T_BOOLEAN:
            return new NewArrayInstruction(JBaseType.BOOLEAN);
          case IOpCodes.T_CHAR:
            return new NewArrayInstruction(JBaseType.CHAR);
          case IOpCodes.T_FLOAT:
            return new NewArrayInstruction(JBaseType.FLOAT);
          case IOpCodes.T_DOUBLE:
            return new NewArrayInstruction(JBaseType.DOUBLE);
          case IOpCodes.T_BYTE:
            return new NewArrayInstruction(JBaseType.BYTE);
          case IOpCodes.T_SHORT:
            return new NewArrayInstruction(JBaseType.SHORT);
          case IOpCodes.T_INT:
            return new NewArrayInstruction(JBaseType.INT);
          case IOpCodes.T_LONG:
          default:
            return new NewArrayInstruction(JBaseType.LONG);
        }
      default:
        throw new UnsupportedInstructionException(opcode);
    }
  }

  public static Instruction fromVarInsn(int opcode, int var)
      throws UnsupportedInstructionException {
    switch (opcode) {
      case IOpCodes.ILOAD:
        return ILoadInstruction.createOptimal(var);
      case IOpCodes.LLOAD:
        return LLoadInstruction.createOptimal(var);
      case IOpCodes.ALOAD:
        return ALoadInstruction.createOptimal(var);
      case IOpCodes.ISTORE:
        return IStoreInstruction.createOptimal(var);
      case IOpCodes.LSTORE:
        return LStoreInstruction.createOptimal(var);
      case IOpCodes.ASTORE:
        return AStoreInstruction.createOptimal(var);
      default:
        throw new UnsupportedInstructionException(opcode);
    }
  }

  public static Instruction fromTypeInsn(int opcode, JReferenceType type)
      throws UnsupportedInstructionException {
    switch (opcode) {
      case IOpCodes.NEW:
        return new NewInstruction(type);
      case IOpCodes.ANEWARRAY:
        return new ANewArrayInstruction(type);
      case IOpCodes.CHECKCAST:
        return new CheckCastInstruction(type);
      case IOpCodes.INSTANCEOF:
        return new InstanceOfInstruction(type);
      default:
        throw new UnsupportedInstructionException(opcode);
    }
  }

  public static Instruction fromFieldInsn(
      int opcode,
      JClassType owner,
      String name,
      JType type) throws UnsupportedInstructionException {
    switch (opcode) {
      case IOpCodes.GETFIELD:
        return new GetFieldInstruction(owner, name, type);
      case IOpCodes.PUTFIELD:
        return new PutFieldInstruction(owner, name, type);
      case IOpCodes.GETSTATIC:
        return new GetStaticInstruction(owner, name, type);
      case IOpCodes.PUTSTATIC:
        return new PutStaticInstruction(owner, name, type);
      default:
        throw new UnsupportedInstructionException(opcode);
    }
  }

  public static Instruction fromMethodInsn(
      int opcode,
      JReferenceType owner,
      String name,
      JType returnType,
      JType[] parameterTypes) throws UnsupportedInstructionException {
    switch (opcode) {
      case IOpCodes.INVOKEVIRTUAL:
        return new InvokeVirtualInstruction(
            owner,
            name,
            returnType,
            parameterTypes);
      case IOpCodes.INVOKESTATIC:
        return new InvokeStaticInstruction(
            owner,
            name,
            returnType,
            parameterTypes);
      case IOpCodes.INVOKESPECIAL:
        return new InvokeSpecialInstruction(
            owner,
            name,
            returnType,
            parameterTypes);
      case IOpCodes.INVOKEINTERFACE:
        return new InvokeInterfaceInstruction(
            owner,
            name,
            returnType,
            parameterTypes);
      default:
        throw new UnsupportedInstructionException(opcode);
    }
  }

  public static Instruction fromJumpInsn(int opcode, InstructionHandle target)
      throws UnsupportedInstructionException {
    switch (opcode) {
      case IOpCodes.IF_ICMPEQ:
        return IfICmpInstruction.createEqual(target);
      case IOpCodes.IF_ICMPNE:
        return IfICmpInstruction.createNotEqual(target);
      case IOpCodes.IF_ICMPLT:
        return IfICmpInstruction.createLower(target);
      case IOpCodes.IF_ICMPGE:
        return IfICmpInstruction.createGreaterEqual(target);
      case IOpCodes.IF_ICMPGT:
        return IfICmpInstruction.createGreater(target);
      case IOpCodes.IF_ICMPLE:
        return IfICmpInstruction.createLowerEqual(target);
      case IOpCodes.IF_ACMPEQ:
        return IfACmpInstruction.createEqual(target);
      case IOpCodes.IF_ACMPNE:
        return IfACmpInstruction.createNotEqual(target);
      case IOpCodes.IFEQ:
        return IfInstruction.createEqual(target);
      case IOpCodes.IFNE:
        return IfInstruction.createNotEqual(target);
      case IOpCodes.IFLT:
        return IfInstruction.createLower(target);
      case IOpCodes.IFGE:
        return IfInstruction.createGreaterEqual(target);
      case IOpCodes.IFGT:
        return IfInstruction.createGreater(target);
      case IOpCodes.IFLE:
        return IfInstruction.createLowerEqual(target);
      case IOpCodes.IFNONNULL:
        return new IfNonNullInstruction(target);
      case IOpCodes.IFNULL:
        return new IfNullInstruction(target);
      case IOpCodes.GOTO:
      case IOpCodes.GOTO_W:
        return new GotoInstruction(target);
      default:
        throw new UnsupportedInstructionException(opcode);
    }
  }

  public static Instruction fromLdcInsn(Object cst)
      throws UnsupportedInstructionException {
    if (cst instanceof Type) {
      Type type = (Type) cst;
      cst = JType.fromDescriptor(type.getDescriptor());
    }
    return new LdcInstruction(cst);
  }

  public static Instruction fromIincInsn(int var, int increment)
      throws UnsupportedInstructionException {
    return new IIncInstruction(var, increment);
  }

  public static Instruction fromTableSwitchInsn(
      int min,
      int max,
      InstructionHandle dflt,
      InstructionHandle[] targets) throws UnsupportedInstructionException {
    return new TableSwitchInstruction(min, max, dflt, targets);
  }

  public static Instruction fromLookupSwitchInsn(
      InstructionHandle dflt,
      int[] keys,
      InstructionHandle[] targets) throws UnsupportedInstructionException {
    return new LookupSwitchInstruction(dflt, keys, targets);
  }

  public static Instruction fromMultiANewArrayInsn(
      JArrayType type,
      int dimensionCount) throws UnsupportedInstructionException {
    return new MultiANewArrayInstruction(type, dimensionCount);
  }
}
