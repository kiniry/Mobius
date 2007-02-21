package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.Opcodes;


public class VALoadInstruction extends Instruction {

  private static final String[] RUNTIME_EXCEPTIONS = new String[] {
    "java.lang.NullPointerException",
    "java.lang.ArrayIndexOutOfBoundsException"
  };

  public static final VALoadInstruction IALOAD =
    new VALoadInstruction(Opcodes.IALOAD);

  public static final VALoadInstruction SALOAD =
    new VALoadInstruction(Opcodes.SALOAD);

  public static final VALoadInstruction BALOAD =
    new VALoadInstruction(Opcodes.BALOAD);

  public static final VALoadInstruction CALOAD =
    new VALoadInstruction(Opcodes.CALOAD);

  private VALoadInstruction(int opcode) {
    super(opcode);
  }

  public String[] getRuntimeExceptions() {
    return RUNTIME_EXCEPTIONS;
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitVALoadInstruction(this);
  }

  public String toString() {
    return Opcodes.NAMES[opcode];
  }
}
