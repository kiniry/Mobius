package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.Opcodes;


public class LCmpInstruction extends Instruction {

  public static final LCmpInstruction LCMP = new LCmpInstruction();

  private LCmpInstruction() {
    super(Opcodes.LCMP);
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitLCmpInstruction(this);
  }

  public String toString() {
    return Opcodes.NAMES[opcode];
  }
}
