package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.Opcodes;


public class SwapInstruction extends Instruction {

  public static final SwapInstruction SWAP = new SwapInstruction();

  private SwapInstruction() {
    super(Opcodes.SWAP);
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitSwapInstruction(this);
  }

  public String toString() {
    return Opcodes.NAMES[opcode];
  }
}
