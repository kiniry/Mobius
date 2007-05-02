package b2bpl.bytecode.instructions;

import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.IOpCodes;


public class INegInstruction extends ArithmeticInstruction {

  public static final INegInstruction INEG = new INegInstruction();

  private INegInstruction() {
    super(IOpCodes.INEG);
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitINegInstruction(this);
  }

  public String toString() {
    return IOpCodes.NAMES[opcode];
  }
}
