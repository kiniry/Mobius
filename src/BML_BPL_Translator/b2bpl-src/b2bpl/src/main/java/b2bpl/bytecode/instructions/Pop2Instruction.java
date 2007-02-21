package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.Opcodes;


public class Pop2Instruction extends Instruction {

  public static final Pop2Instruction POP2 = new Pop2Instruction();

  private Pop2Instruction() {
    super(Opcodes.POP2);
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitPop2Instruction(this);
  }

  public String toString() {
    return Opcodes.NAMES[opcode];
  }
}
