package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.Opcodes;


public class IIncInstruction extends ArithmeticInstruction {

  private final int index;

  private final int constant;

  public IIncInstruction(int index, int constant) {
    super(Opcodes.IINC);
    this.index = index;
    this.constant = constant;
  }

  public int getIndex() {
    return index;
  }

  public int getConstant() {
    return constant;
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitIIncInstruction(this);
  }

  public String toString() {
    return Opcodes.NAMES[opcode] + " " + index + ", " + constant;
  }
}
