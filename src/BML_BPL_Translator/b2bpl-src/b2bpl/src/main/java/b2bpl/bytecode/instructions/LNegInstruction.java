package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.Opcodes;


public class LNegInstruction extends ArithmeticInstruction {

  public static final LNegInstruction LNEG = new LNegInstruction();

  private LNegInstruction() {
    super(Opcodes.LNEG);
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitLNegInstruction(this);
  }

  public String toString() {
    return Opcodes.NAMES[opcode];
  }
}
