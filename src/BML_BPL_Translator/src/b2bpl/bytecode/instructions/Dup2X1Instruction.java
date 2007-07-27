package b2bpl.bytecode.instructions;

import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.IOpCodes;


public class Dup2X1Instruction extends Instruction {

  public static final Dup2X1Instruction DUP2_X1 = new Dup2X1Instruction();

  private Dup2X1Instruction() {
    super(IOpCodes.DUP2_X1);
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitDup2X1Instruction(this);
  }

  public String toString() {
    return IOpCodes.NAMES[opcode];
  }
}
