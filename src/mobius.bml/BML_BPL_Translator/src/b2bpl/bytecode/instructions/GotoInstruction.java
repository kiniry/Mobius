package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionHandle;
import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.IOpCodes;


public class GotoInstruction extends BranchInstruction {

  public GotoInstruction(InstructionHandle target) {
    super(IOpCodes.GOTO, target);
  }

  public boolean isUnconditionalBranch() {
    return true;
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitGotoInstruction(this);
  }
}
