package b2bpl.bytecode.instructions;

import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.IOpCodes;


public class VAStoreInstruction extends Instruction {

  private static final String[] RUNTIME_EXCEPTIONS = new String[] {
    "java.lang.NullPointerException",
    "java.lang.ArrayIndexOutOfBoundsException"
  };

  public static final VAStoreInstruction IASTORE =
    new VAStoreInstruction(IOpCodes.IASTORE);

  public static final VAStoreInstruction SASTORE =
    new VAStoreInstruction(IOpCodes.SASTORE);

  public static final VAStoreInstruction BASTORE =
    new VAStoreInstruction(IOpCodes.BASTORE);

  public static final VAStoreInstruction CASTORE =
    new VAStoreInstruction(IOpCodes.CASTORE);

  public static final VAStoreInstruction LASTORE =
    new VAStoreInstruction(IOpCodes.LASTORE);

  private VAStoreInstruction(int opcode) {
    super(opcode);
  }

  public String[] getRuntimeExceptions() {
    return RUNTIME_EXCEPTIONS;
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitVAStoreInstruction(this);
  }

  public String toString() {
    return IOpCodes.NAMES[opcode];
  }
}
