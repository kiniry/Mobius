package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.Opcodes;


public class NopInstruction extends Instruction {

  public static final NopInstruction NOP = new NopInstruction();

  private NopInstruction() {
    super(Opcodes.NOP);
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitNopInstruction(this);
  }

  public String toString() {
    return Opcodes.NAMES[opcode];
  }
}
