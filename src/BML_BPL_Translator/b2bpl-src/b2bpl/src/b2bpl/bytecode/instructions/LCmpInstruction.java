package b2bpl.bytecode.instructions;

import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.IOpCodes;


public class LCmpInstruction extends Instruction {

  public static final LCmpInstruction LCMP = new LCmpInstruction();

  private LCmpInstruction() {
    super(IOpCodes.LCMP);
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitLCmpInstruction(this);
  }

  public String toString() {
    return IOpCodes.NAMES[opcode];
  }
}
