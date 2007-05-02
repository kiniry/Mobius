package b2bpl.bytecode.instructions;

import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.IOpCodes;


public class PopInstruction extends Instruction {

  public static final PopInstruction POP = new PopInstruction();

  private PopInstruction() {
    super(IOpCodes.POP);
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitPopInstruction(this);
  }

  public String toString() {
    return IOpCodes.NAMES[opcode];
  }
}
