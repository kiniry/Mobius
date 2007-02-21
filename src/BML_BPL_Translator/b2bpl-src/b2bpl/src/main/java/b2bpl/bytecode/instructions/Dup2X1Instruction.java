package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.Opcodes;


public class Dup2X1Instruction extends Instruction {

  public static final Dup2X1Instruction DUP2_X1 = new Dup2X1Instruction();

  private Dup2X1Instruction() {
    super(Opcodes.DUP2_X1);
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitDup2X1Instruction(this);
  }

  public String toString() {
    return Opcodes.NAMES[opcode];
  }
}
