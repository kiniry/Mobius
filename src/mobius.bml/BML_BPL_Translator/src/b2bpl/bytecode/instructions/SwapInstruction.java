package b2bpl.bytecode.instructions;

import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.IOpCodes;


public class SwapInstruction extends Instruction {

  public static final SwapInstruction SWAP = new SwapInstruction();

  private SwapInstruction() {
    super(IOpCodes.SWAP);
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitSwapInstruction(this);
  }

  public String toString() {
    return IOpCodes.NAMES[opcode];
  }
}
