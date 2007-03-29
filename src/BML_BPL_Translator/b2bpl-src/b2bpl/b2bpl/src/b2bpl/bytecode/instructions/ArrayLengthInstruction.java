package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.Opcodes;


public class ArrayLengthInstruction extends Instruction {

  private static final String[] RUNTIME_EXCEPTIONS = new String[] {
    "java.lang.NullPointerException"
  };

  public static final ArrayLengthInstruction ARRAYLENGTH =
    new ArrayLengthInstruction();

  private ArrayLengthInstruction() {
    super(Opcodes.ARRAYLENGTH);
  }

  public String[] getRuntimeExceptions() {
    return RUNTIME_EXCEPTIONS;
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitArrayLengthInstruction(this);
  }

  public String toString() {
    return Opcodes.NAMES[opcode];
  }
}
