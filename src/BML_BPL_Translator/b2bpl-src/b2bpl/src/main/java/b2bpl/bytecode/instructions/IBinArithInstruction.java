package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.Opcodes;


public class IBinArithInstruction extends ArithmeticInstruction {

  private static String[] runtimeExceptions;

  public static final IBinArithInstruction IADD =
    new IBinArithInstruction(Opcodes.IADD);

  public static final IBinArithInstruction ISUB =
    new IBinArithInstruction(Opcodes.ISUB);

  public static final IBinArithInstruction IMUL =
    new IBinArithInstruction(Opcodes.IMUL);

  public static final IBinArithInstruction IDIV =
    new IBinArithInstruction(Opcodes.IDIV);

  public static final IBinArithInstruction IREM =
    new IBinArithInstruction(Opcodes.IREM);

  private IBinArithInstruction(int opcode) {
    super(opcode);
  }

  public String[] getRuntimeExceptions() {
    if (runtimeExceptions == null) {
      if (equals(IDIV) || equals(IREM)) {
        runtimeExceptions = new String[] { "java.lang.ArithmeticException" };
      } else {
        runtimeExceptions = new String[0];
      }
    }
    return runtimeExceptions;
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitIBinArithInstruction(this);
  }

  public String toString() {
    return Opcodes.NAMES[opcode];
  }
}
