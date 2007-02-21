package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.Opcodes;


public class IReturnInstruction extends AbstractReturnInstruction {

  public static final IReturnInstruction IRETURN = new IReturnInstruction();

  private IReturnInstruction() {
    super(Opcodes.IRETURN);
  }

  public boolean isUnconditionalBranch() {
    return true;
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitIReturnInstruction(this);
  }

  public String toString() {
    return Opcodes.NAMES[opcode];
  }
}
