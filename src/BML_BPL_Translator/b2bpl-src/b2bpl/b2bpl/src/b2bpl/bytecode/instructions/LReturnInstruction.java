package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.Opcodes;


public class LReturnInstruction extends AbstractReturnInstruction {

  public static final LReturnInstruction LRETURN = new LReturnInstruction();

  private LReturnInstruction() {
    super(Opcodes.LRETURN);
  }

  public boolean isUnconditionalBranch() {
    return true;
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitLReturnInstruction(this);
  }

  public String toString() {
    return Opcodes.NAMES[opcode];
  }
}
