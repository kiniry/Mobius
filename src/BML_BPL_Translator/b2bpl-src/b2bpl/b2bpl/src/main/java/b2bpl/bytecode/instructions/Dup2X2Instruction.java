package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.Opcodes;


public class Dup2X2Instruction extends Instruction {

  public static final Dup2X2Instruction DUP2_X2 = new Dup2X2Instruction();

  private Dup2X2Instruction() {
    super(Opcodes.DUP2_X2);
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitDup2X2Instruction(this);
  }

  public String toString() {
    return Opcodes.NAMES[opcode];
  }
}
