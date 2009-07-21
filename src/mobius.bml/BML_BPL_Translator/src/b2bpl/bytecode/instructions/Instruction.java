package b2bpl.bytecode.instructions;

import b2bpl.bytecode.IInstructionVisitor;


public abstract class Instruction {

  protected final int opcode;

  private static final String[] NO_RUNTIME_EXCEPTIONS = new String[0];

  public Instruction(int opcode) {
    this.opcode = opcode;
  }

  public int getOpcode() {
    return opcode;
  }

  public boolean isUnconditionalBranch() {
    return false;
  }

  public String[] getRuntimeExceptions() {
    return NO_RUNTIME_EXCEPTIONS;
  }

  public abstract void accept(IInstructionVisitor visitor);
}
