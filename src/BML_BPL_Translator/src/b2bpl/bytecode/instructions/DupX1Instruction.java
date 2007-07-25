package b2bpl.bytecode.instructions;

import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.IOpCodes;


public class DupX1Instruction extends Instruction {

  public static final DupX1Instruction DUP_X1 = new DupX1Instruction();

  private DupX1Instruction() {
    super(IOpCodes.DUP_X1);
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitDupX1Instruction(this);
  }

  public String toString() {
    return IOpCodes.NAMES[opcode];
  }
}
