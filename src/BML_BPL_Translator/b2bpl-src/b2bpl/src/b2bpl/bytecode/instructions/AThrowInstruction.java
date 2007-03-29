package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.Opcodes;


public class AThrowInstruction extends Instruction {

  private static final String[] RUNTIME_EXCEPTIONS = new String[] {
    "java.lang.NullPointerException"
  };

  public static final AThrowInstruction ATHROW = new AThrowInstruction();

  private AThrowInstruction() {
    super(Opcodes.ATHROW);
  }

  public boolean isUnconditionalBranch() {
    return true;
  }

  public String[] getRuntimeExceptions() {
    return RUNTIME_EXCEPTIONS;
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitAThrowInstruction(this);
  }

  public String toString() {
    return Opcodes.NAMES[opcode];
  }
}
