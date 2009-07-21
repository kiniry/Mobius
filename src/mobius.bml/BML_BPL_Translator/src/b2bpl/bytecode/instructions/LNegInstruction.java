package b2bpl.bytecode.instructions;

import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.IOpCodes;


public class LNegInstruction extends ArithmeticInstruction {

  public static final LNegInstruction LNEG = new LNegInstruction();

  private LNegInstruction() {
    super(IOpCodes.LNEG);
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitLNegInstruction(this);
  }

  public String toString() {
    return IOpCodes.NAMES[opcode];
  }
}
