package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.Opcodes;


public class AReturnInstruction extends AbstractReturnInstruction {

  public static final AReturnInstruction ARETURN = new AReturnInstruction();

  private AReturnInstruction() {
    super(Opcodes.ARETURN);
  }

  public boolean isUnconditionalBranch() {
    return true;
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitAReturnInstruction(this);
  }

  public String toString() {
    return Opcodes.NAMES[opcode];
  }
}
