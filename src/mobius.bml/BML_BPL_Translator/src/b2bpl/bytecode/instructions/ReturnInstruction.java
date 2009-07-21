package b2bpl.bytecode.instructions;

import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.IOpCodes;


public class ReturnInstruction extends AbstractReturnInstruction {

  public static final ReturnInstruction RETURN = new ReturnInstruction();

  private ReturnInstruction() {
    super(IOpCodes.RETURN);
  }

  public boolean isUnconditionalBranch() {
    return true;
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitReturnInstruction(this);
  }

  public String toString() {
    return IOpCodes.NAMES[opcode];
  }
}
