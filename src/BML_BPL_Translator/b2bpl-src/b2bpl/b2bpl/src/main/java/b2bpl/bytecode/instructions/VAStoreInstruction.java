package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.Opcodes;


public class VAStoreInstruction extends Instruction {

  private static final String[] RUNTIME_EXCEPTIONS = new String[] {
    "java.lang.NullPointerException",
    "java.lang.ArrayIndexOutOfBoundsException"
  };

  public static final VAStoreInstruction IASTORE =
    new VAStoreInstruction(Opcodes.IASTORE);

  public static final VAStoreInstruction SASTORE =
    new VAStoreInstruction(Opcodes.SASTORE);

  public static final VAStoreInstruction BASTORE =
    new VAStoreInstruction(Opcodes.BASTORE);

  public static final VAStoreInstruction CASTORE =
    new VAStoreInstruction(Opcodes.CASTORE);

  public static final VAStoreInstruction LASTORE =
    new VAStoreInstruction(Opcodes.LASTORE);

  private VAStoreInstruction(int opcode) {
    super(opcode);
  }

  public String[] getRuntimeExceptions() {
    return RUNTIME_EXCEPTIONS;
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitVAStoreInstruction(this);
  }

  public String toString() {
    return Opcodes.NAMES[opcode];
  }
}
