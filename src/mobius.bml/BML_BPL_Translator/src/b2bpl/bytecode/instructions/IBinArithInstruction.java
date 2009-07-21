package b2bpl.bytecode.instructions;

import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.IOpCodes;


public class IBinArithInstruction extends ArithmeticInstruction {

  private static String[] runtimeExceptions;

  public static final IBinArithInstruction IADD =
    new IBinArithInstruction(IOpCodes.IADD);

  public static final IBinArithInstruction ISUB =
    new IBinArithInstruction(IOpCodes.ISUB);

  public static final IBinArithInstruction IMUL =
    new IBinArithInstruction(IOpCodes.IMUL);

  public static final IBinArithInstruction IDIV =
    new IBinArithInstruction(IOpCodes.IDIV);

  public static final IBinArithInstruction IREM =
    new IBinArithInstruction(IOpCodes.IREM);

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

  public void accept(IInstructionVisitor visitor) {
    visitor.visitIBinArithInstruction(this);
  }

  public String toString() {
    return IOpCodes.NAMES[opcode];
  }
}
