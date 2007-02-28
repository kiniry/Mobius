package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.Opcodes;


public class INegInstruction extends ArithmeticInstruction {

  public static final INegInstruction INEG = new INegInstruction();

  private INegInstruction() {
    super(Opcodes.INEG);
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitINegInstruction(this);
  }

  public String toString() {
    return Opcodes.NAMES[opcode];
  }
}
