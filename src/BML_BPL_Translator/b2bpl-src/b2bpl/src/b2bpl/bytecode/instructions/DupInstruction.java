package b2bpl.bytecode.instructions;

import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.IOpCodes;


public class DupInstruction extends Instruction {

  public static final DupInstruction DUP = new DupInstruction();

  private DupInstruction() {
    super(IOpCodes.DUP);
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitDupInstruction(this);
  }

  public String toString() {
    return IOpCodes.NAMES[opcode];
  }
}
