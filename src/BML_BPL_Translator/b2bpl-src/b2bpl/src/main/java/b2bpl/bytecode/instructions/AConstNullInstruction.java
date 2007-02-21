package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.Opcodes;


public class AConstNullInstruction extends Instruction {

  public static final AConstNullInstruction ACONST_NULL =
    new AConstNullInstruction();

  private AConstNullInstruction() {
    super(Opcodes.ACONST_NULL);
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitAConstNullInstruction(this);
  }

  public String toString() {
    return Opcodes.NAMES[opcode];
  }
}
