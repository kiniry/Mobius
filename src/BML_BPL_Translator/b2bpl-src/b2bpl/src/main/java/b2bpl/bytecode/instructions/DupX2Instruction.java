package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.Opcodes;


public class DupX2Instruction extends Instruction {

  public static final DupX2Instruction DUP_X2 = new DupX2Instruction();

  private DupX2Instruction() {
    super(Opcodes.DUP_X2);
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitDupX2Instruction(this);
  }

  public String toString() {
    return Opcodes.NAMES[opcode];
  }
}
