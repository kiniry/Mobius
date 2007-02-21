package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionHandle;
import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.Opcodes;


public class GotoInstruction extends BranchInstruction {

  public GotoInstruction(InstructionHandle target) {
    super(Opcodes.GOTO, target);
  }

  public boolean isUnconditionalBranch() {
    return true;
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitGotoInstruction(this);
  }
}
