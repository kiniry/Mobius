package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.Opcodes;


public class PopInstruction extends Instruction {

  public static final PopInstruction POP = new PopInstruction();

  private PopInstruction() {
    super(Opcodes.POP);
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitPopInstruction(this);
  }

  public String toString() {
    return Opcodes.NAMES[opcode];
  }
}
