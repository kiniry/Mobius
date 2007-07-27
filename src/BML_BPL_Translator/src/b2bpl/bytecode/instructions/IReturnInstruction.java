package b2bpl.bytecode.instructions;

import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.IOpCodes;


public class IReturnInstruction extends AbstractReturnInstruction {

  public static final IReturnInstruction IRETURN = new IReturnInstruction();

  private IReturnInstruction() {
    super(IOpCodes.IRETURN);
  }

  public boolean isUnconditionalBranch() {
    return true;
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitIReturnInstruction(this);
  }

  public String toString() {
    return IOpCodes.NAMES[opcode];
  }
}
