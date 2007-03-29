package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.Opcodes;


public class AALoadInstruction extends Instruction {

  private static final String[] RUNTIME_EXCEPTIONS = new String[] {
    "java.lang.NullPointerException",
    "java.lang.ArrayIndexOutOfBoundsException"
  };

  public static final AALoadInstruction AALOAD = new AALoadInstruction();

  private AALoadInstruction() {
    super(Opcodes.AALOAD);
  }

  public String[] getRuntimeExceptions() {
    return RUNTIME_EXCEPTIONS;
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitAALoadInstruction(this);
  }

  public String toString() {
    return Opcodes.NAMES[opcode];
  }
}
