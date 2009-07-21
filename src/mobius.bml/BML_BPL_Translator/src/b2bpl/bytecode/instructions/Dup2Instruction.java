package b2bpl.bytecode.instructions;

import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.IOpCodes;


public class Dup2Instruction extends Instruction {

  public static final Dup2Instruction DUP2 = new Dup2Instruction();

  private Dup2Instruction() {
    super(IOpCodes.DUP2);
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitDup2Instruction(this);
  }

  public String toString() {
    return IOpCodes.NAMES[opcode];
  }
}
