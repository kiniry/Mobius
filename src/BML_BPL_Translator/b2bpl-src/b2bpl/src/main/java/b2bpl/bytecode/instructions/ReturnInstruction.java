package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.Opcodes;


public class ReturnInstruction extends AbstractReturnInstruction {

  public static final ReturnInstruction RETURN = new ReturnInstruction();

  private ReturnInstruction() {
    super(Opcodes.RETURN);
  }

  public boolean isUnconditionalBranch() {
    return true;
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitReturnInstruction(this);
  }

  public String toString() {
    return Opcodes.NAMES[opcode];
  }
}
