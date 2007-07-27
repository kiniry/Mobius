package b2bpl.bytecode.instructions;

import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.IOpCodes;


public class AALoadInstruction extends Instruction {

  private static final String[] RUNTIME_EXCEPTIONS = new String[] {
    "java.lang.NullPointerException",
    "java.lang.ArrayIndexOutOfBoundsException"
  };

  public static final AALoadInstruction AALOAD = new AALoadInstruction();

  private AALoadInstruction() {
    super(IOpCodes.AALOAD);
  }

  public String[] getRuntimeExceptions() {
    return RUNTIME_EXCEPTIONS;
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitAALoadInstruction(this);
  }

  public String toString() {
    return IOpCodes.NAMES[opcode];
  }
}
