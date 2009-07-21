package b2bpl.bytecode.instructions;

import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.IOpCodes;


public class Pop2Instruction extends Instruction {

  public static final Pop2Instruction POP2 = new Pop2Instruction();

  private Pop2Instruction() {
    super(IOpCodes.POP2);
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitPop2Instruction(this);
  }

  public String toString() {
    return IOpCodes.NAMES[opcode];
  }
}
