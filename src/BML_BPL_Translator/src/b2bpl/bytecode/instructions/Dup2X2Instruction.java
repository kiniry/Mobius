package b2bpl.bytecode.instructions;

import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.IOpCodes;


public class Dup2X2Instruction extends Instruction {

  public static final Dup2X2Instruction DUP2_X2 = new Dup2X2Instruction();

  private Dup2X2Instruction() {
    super(IOpCodes.DUP2_X2);
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitDup2X2Instruction(this);
  }

  public String toString() {
    return IOpCodes.NAMES[opcode];
  }
}
