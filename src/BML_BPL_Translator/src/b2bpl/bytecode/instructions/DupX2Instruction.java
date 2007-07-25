package b2bpl.bytecode.instructions;

import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.IOpCodes;


public class DupX2Instruction extends Instruction {

  public static final DupX2Instruction DUP_X2 = new DupX2Instruction();

  private DupX2Instruction() {
    super(IOpCodes.DUP_X2);
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitDupX2Instruction(this);
  }

  public String toString() {
    return IOpCodes.NAMES[opcode];
  }
}
