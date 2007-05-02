package b2bpl.bytecode.instructions;

import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.IOpCodes;


public class AReturnInstruction extends AbstractReturnInstruction {

  public static final AReturnInstruction ARETURN = new AReturnInstruction();

  private AReturnInstruction() {
    super(IOpCodes.ARETURN);
  }

  public boolean isUnconditionalBranch() {
    return true;
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitAReturnInstruction(this);
  }

  public String toString() {
    return IOpCodes.NAMES[opcode];
  }
}
