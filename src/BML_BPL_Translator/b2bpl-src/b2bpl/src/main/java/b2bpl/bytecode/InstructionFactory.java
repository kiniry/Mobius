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
import b2bpl.bytecode.instructions.VALoadInstruction;
import b2bpl.bytecode.instructions.VAStoreInstruction;
import b2bpl.bytecode.instructions.IBinArithInstruction;
import b2bpl.bytecode.instructions.IBitwiseInstruction;
import b2bpl.bytecode.instructions.IConstantInstruction;
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
import b2bpl.bytecode.instructions.VCastInstruction;


public class InstructionFactory {

  public static Instruction fromInsn(int opcode)
      throws UnsupportedInstructionException {
    switch (opcode) {
      case Opcodes.NOP:
        return NopInstruction.NOP;
      case Opcodes.ICONST_M1:
        return IConstantInstruction.ICONST_M1;
      case Opcodes.ICONST_0:
        return IConstantInstruction.ICONST_0;
      case Opcodes.ICONST_1:
        return IConstantInstruction.ICONST_1;
      case Opcodes.ICONST_2:
        return IConstantInstruction.ICONST_2;
      case Opcodes.ICONST_3:
        return IConstantInstruction.ICONST_3;
      case Opcodes.ICONST_4:
        return IConstantInstruction.ICONST_4;
      case Opcodes.ICONST_5:
        return IConstantInstruction.ICONST_5;
      case Opcodes.ACONST_NULL:
        return AConstNullInstruction.ACONST_NULL;
      case Opcodes.IALOAD:
        return VALoadInstruction.IALOAD;
      case Opcodes.SALOAD:
        return VALoadInstruction.SALOAD;
      case Opcodes.BALOAD:
        return VALoadInstruction.BALOAD;
      case Opcodes.CALOAD:
        return VALoadInstruction.CALOAD;
      case Opcodes.AALOAD:
        return AALoadInstruction.AALOAD;
      case Opcodes.IASTORE:
        return VAStoreInstruction.IASTORE;
      case Opcodes.SASTORE:
        return VAStoreInstruction.SASTORE;
      case Opcodes.BASTORE:
        return VAStoreInstruction.BASTORE;
      case Opcodes.CASTORE:
        return VAStoreInstruction.CASTORE;
      case Opcodes.AASTORE:
        return AAStoreInstruction.AASTORE;
      case Opcodes.ARRAYLENGTH:
        return ArrayLengthInstruction.ARRAYLENGTH;
      case Opcodes.IADD:
        return IBinArithInstruction.IADD;
      case Opcodes.ISUB:
        return IBinArithInstruction.ISUB;
      case Opcodes.IMUL:
        return IBinArithInstruction.IMUL;
      case Opcodes.IDIV:
        return IBinArithInstruction.IDIV;
      case Opcodes.IREM:
        return IBinArithInstruction.IREM;
      case Opcodes.INEG:
        return INegInstruction.INEG;
      case Opcodes.ISHL:
        return IBitwiseInstruction.ISHL;
      case Opcodes.ISHR:
        return IBitwiseInstruction.ISHR;
      case Opcodes.IUSHR:
        return IBitwiseInstruction.IUSHR;
      case Opcodes.IAND:
        return IBitwiseInstruction.IAND;
      case Opcodes.IOR:
        return IBitwiseInstruction.IOR;
      case Opcodes.IXOR:
        return IBitwiseInstruction.IXOR;
      case Opcodes.I2S:
        return VCastInstruction.I2S;
      case Opcodes.I2B:
        return VCastInstruction.I2B;
      case Opcodes.I2C:
        return VCastInstruction.I2C;
      case Opcodes.RETURN:
        return ReturnInstruction.RETURN;
      case Opcodes.IRETURN:
        return IReturnInstruction.IRETURN;
      case Opcodes.ARETURN:
        return AReturnInstruction.ARETURN;
      case Opcodes.ATHROW:
        return AThrowInstruction.ATHROW;
      case Opcodes.POP:
        return PopInstruction.POP;
      case Opcodes.POP2:
        return Pop2Instruction.POP2;
      case Opcodes.SWAP:
        return SwapInstruction.SWAP;
      case Opcodes.DUP:
        return DupInstruction.DUP;
      case Opcodes.DUP2:
        return Dup2Instruction.DUP2;
      case Opcodes.DUP_X1:
        return DupX1Instruction.DUP_X1;
      case Opcodes.DUP_X2:
        return DupX2Instruction.DUP_X2;
      case Opcodes.DUP2_X1:
        return Dup2X1Instruction.DUP2_X1;
      case Opcodes.DUP2_X2:
        return Dup2X2Instruction.DUP2_X2;
      default:
        throw new UnsupportedInstructionException(opcode);
    }
  }

  public static Instruction fromIntInsn(int opcode, int operand)
      throws UnsupportedInstructionException {
    switch (opcode) {
      case Opcodes.BIPUSH:
      case Opcodes.SIPUSH:
        return IConstantInstruction.createOptimal(operand);
      case Opcodes.NEWARRAY:
        switch (operand) {
          case Opcodes.T_BOOLEAN:
            return new NewArrayInstruction(JBaseType.BOOLEAN);
          case Opcodes.T_CHAR:
            return new NewArrayInstruction(JBaseType.CHAR);
          case Opcodes.T_FLOAT:
            return new NewArrayInstruction(JBaseType.FLOAT);
          case Opcodes.T_DOUBLE:
            return new NewArrayInstruction(JBaseType.DOUBLE);
          case Opcodes.T_BYTE:
            return new NewArrayInstruction(JBaseType.BYTE);
          case Opcodes.T_SHORT:
            return new NewArrayInstruction(JBaseType.SHORT);
          case Opcodes.T_INT:
            return new NewArrayInstruction(JBaseType.INT);
          case Opcodes.T_LONG:
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
      case Opcodes.ILOAD:
        return ILoadInstruction.createOptimal(var);
      case Opcodes.ALOAD:
        return ALoadInstruction.createOptimal(var);
      case Opcodes.ISTORE:
        return IStoreInstruction.createOptimal(var);
      case Opcodes.ASTORE:
        return AStoreInstruction.createOptimal(var);
      default:
        throw new UnsupportedInstructionException(opcode);
    }
  }

  public static Instruction fromTypeInsn(int opcode, JReferenceType type)
      throws UnsupportedInstructionException {
    switch (opcode) {
      case Opcodes.NEW:
        return new NewInstruction(type);
      case Opcodes.ANEWARRAY:
        return new ANewArrayInstruction(type);
      case Opcodes.CHECKCAST:
        return new CheckCastInstruction(type);
      case Opcodes.INSTANCEOF:
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
      case Opcodes.GETFIELD:
        return new GetFieldInstruction(owner, name, type);
      case Opcodes.PUTFIELD:
        return new PutFieldInstruction(owner, name, type);
      case Opcodes.GETSTATIC:
        return new GetStaticInstruction(owner, name, type);
      case Opcodes.PUTSTATIC:
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
      case Opcodes.INVOKEVIRTUAL:
        return new InvokeVirtualInstruction(
            owner,
            name,
            returnType,
            parameterTypes);
      case Opcodes.INVOKESTATIC:
        return new InvokeStaticInstruction(
            owner,
            name,
            returnType,
            parameterTypes);
      case Opcodes.INVOKESPECIAL:
        return new InvokeSpecialInstruction(
            owner,
            name,
            returnType,
            parameterTypes);
      case Opcodes.INVOKEINTERFACE:
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
      case Opcodes.IF_ICMPEQ:
        return IfICmpInstruction.createEqual(target);
      case Opcodes.IF_ICMPNE:
        return IfICmpInstruction.createNotEqual(target);
      case Opcodes.IF_ICMPLT:
        return IfICmpInstruction.createLower(target);
      case Opcodes.IF_ICMPGE:
        return IfICmpInstruction.createGreaterEqual(target);
      case Opcodes.IF_ICMPGT:
        return IfICmpInstruction.createGreater(target);
      case Opcodes.IF_ICMPLE:
        return IfICmpInstruction.createLowerEqual(target);
      case Opcodes.IF_ACMPEQ:
        return IfACmpInstruction.createEqual(target);
      case Opcodes.IF_ACMPNE:
        return IfACmpInstruction.createNotEqual(target);
      case Opcodes.IFEQ:
        return IfInstruction.createEqual(target);
      case Opcodes.IFNE:
        return IfInstruction.createNotEqual(target);
      case Opcodes.IFLT:
        return IfInstruction.createLower(target);
      case Opcodes.IFGE:
        return IfInstruction.createGreaterEqual(target);
      case Opcodes.IFGT:
        return IfInstruction.createGreater(target);
      case Opcodes.IFLE:
        return IfInstruction.createLowerEqual(target);
      case Opcodes.IFNONNULL:
        return new IfNonNullInstruction(target);
      case Opcodes.IFNULL:
        return new IfNullInstruction(target);
      case Opcodes.GOTO:
      case Opcodes.GOTO_W:
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
