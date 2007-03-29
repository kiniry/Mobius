package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.Opcodes;


public class DupX1Instruction extends Instruction {

  public static final DupX1Instruction DUP_X1 = new DupX1Instruction();

  private DupX1Instruction() {
    super(Opcodes.DUP_X1);
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitDupX1Instruction(this);
  }

  public String toString() {
    return Opcodes.NAMES[opcode];
  }
}
