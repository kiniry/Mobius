package b2bpl.bytecode.instructions;

import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.IOpCodes;


public class AConstNullInstruction extends Instruction {

  public static final AConstNullInstruction ACONST_NULL =
    new AConstNullInstruction();

  private AConstNullInstruction() {
    super(IOpCodes.ACONST_NULL);
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitAConstNullInstruction(this);
  }

  public String toString() {
    return IOpCodes.NAMES[opcode];
  }
}
