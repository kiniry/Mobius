package b2bpl.bytecode.instructions;

import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.IOpCodes;


public class LReturnInstruction extends AbstractReturnInstruction {

  public static final LReturnInstruction LRETURN = new LReturnInstruction();

  private LReturnInstruction() {
    super(IOpCodes.LRETURN);
  }

  public boolean isUnconditionalBranch() {
    return true;
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitLReturnInstruction(this);
  }

  public String toString() {
    return IOpCodes.NAMES[opcode];
  }
}
