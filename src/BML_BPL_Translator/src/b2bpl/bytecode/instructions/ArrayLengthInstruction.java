package b2bpl.bytecode.instructions;

import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.IOpCodes;


public class ArrayLengthInstruction extends Instruction {

  private static final String[] RUNTIME_EXCEPTIONS = new String[] {
    "java.lang.NullPointerException"
  };

  public static final ArrayLengthInstruction ARRAYLENGTH =
    new ArrayLengthInstruction();

  private ArrayLengthInstruction() {
    super(IOpCodes.ARRAYLENGTH);
  }

  public String[] getRuntimeExceptions() {
    return RUNTIME_EXCEPTIONS;
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitArrayLengthInstruction(this);
  }

  public String toString() {
    return IOpCodes.NAMES[opcode];
  }
}
