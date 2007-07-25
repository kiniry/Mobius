package b2bpl.bytecode.instructions;

import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.IOpCodes;


public class IIncInstruction extends ArithmeticInstruction {

  private final int index;

  private final int constant;

  public IIncInstruction(int index, int constant) {
    super(IOpCodes.IINC);
    this.index = index;
    this.constant = constant;
  }

  public int getIndex() {
    return index;
  }

  public int getConstant() {
    return constant;
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitIIncInstruction(this);
  }

  public String toString() {
    return IOpCodes.NAMES[opcode] + " " + index + ", " + constant;
  }
}
