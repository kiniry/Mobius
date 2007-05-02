package b2bpl.bytecode.instructions;

import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.IOpCodes;


public class VALoadInstruction extends Instruction {

  private static final String[] RUNTIME_EXCEPTIONS = new String[] {
    "java.lang.NullPointerException",
    "java.lang.ArrayIndexOutOfBoundsException"
  };

  public static final VALoadInstruction IALOAD =
    new VALoadInstruction(IOpCodes.IALOAD);

  public static final VALoadInstruction SALOAD =
    new VALoadInstruction(IOpCodes.SALOAD);

  public static final VALoadInstruction BALOAD =
    new VALoadInstruction(IOpCodes.BALOAD);

  public static final VALoadInstruction CALOAD =
    new VALoadInstruction(IOpCodes.CALOAD);

  public static final VALoadInstruction LALOAD =
    new VALoadInstruction(IOpCodes.LALOAD);

  private VALoadInstruction(int opcode) {
    super(opcode);
  }

  public String[] getRuntimeExceptions() {
    return RUNTIME_EXCEPTIONS;
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitVALoadInstruction(this);
  }

  public String toString() {
    return IOpCodes.NAMES[opcode];
  }
}
