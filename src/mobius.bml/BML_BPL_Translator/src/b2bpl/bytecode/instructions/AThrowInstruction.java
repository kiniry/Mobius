package b2bpl.bytecode.instructions;

import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.IOpCodes;


public class AThrowInstruction extends Instruction {

  private static final String[] RUNTIME_EXCEPTIONS = new String[] {
    "java.lang.NullPointerException"
  };

  public static final AThrowInstruction ATHROW = new AThrowInstruction();

  private AThrowInstruction() {
    super(IOpCodes.ATHROW);
  }

  public boolean isUnconditionalBranch() {
    return true;
  }

  public String[] getRuntimeExceptions() {
    return RUNTIME_EXCEPTIONS;
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitAThrowInstruction(this);
  }

  public String toString() {
    return IOpCodes.NAMES[opcode];
  }
}
