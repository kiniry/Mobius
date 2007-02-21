package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.Opcodes;


public class DupInstruction extends Instruction {

  public static final DupInstruction DUP = new DupInstruction();

  private DupInstruction() {
    super(Opcodes.DUP);
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitDupInstruction(this);
  }

  public String toString() {
    return Opcodes.NAMES[opcode];
  }
}
