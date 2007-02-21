package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.Opcodes;


public class Dup2Instruction extends Instruction {

  public static final Dup2Instruction DUP2 = new Dup2Instruction();

  private Dup2Instruction() {
    super(Opcodes.DUP2);
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitDup2Instruction(this);
  }

  public String toString() {
    return Opcodes.NAMES[opcode];
  }
}
