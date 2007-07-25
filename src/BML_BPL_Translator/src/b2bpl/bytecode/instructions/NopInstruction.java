package b2bpl.bytecode.instructions;

import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.IOpCodes;


public class NopInstruction extends Instruction {

  public static final NopInstruction NOP = new NopInstruction();

  private NopInstruction() {
    super(IOpCodes.NOP);
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitNopInstruction(this);
  }

  public String toString() {
    return IOpCodes.NAMES[opcode];
  }
}
