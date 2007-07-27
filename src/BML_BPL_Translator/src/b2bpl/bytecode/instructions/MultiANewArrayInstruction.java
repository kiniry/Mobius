package b2bpl.bytecode.instructions;

import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.JArrayType;
import b2bpl.bytecode.IOpCodes;


public class MultiANewArrayInstruction extends Instruction {

  private static final String[] RUNTIME_EXCEPTIONS = new String[] {
    "java.lang.NegativeArraySizeException"
  };

  private final JArrayType type;

  private final int dimensionCount;

  public MultiANewArrayInstruction(JArrayType type, int dimensionCount) {
    super(IOpCodes.MULTIANEWARRAY);
    this.type = type;
    this.dimensionCount = dimensionCount;
  }

  public JArrayType getType() {
    return type;
  }

  public int getDimensionCount() {
    return dimensionCount;
  }

  public String[] getRuntimeExceptions() {
    return RUNTIME_EXCEPTIONS;
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitMultiANewArrayInstruction(this);
  }

  public String toString() {
    return IOpCodes.NAMES[opcode] + " " + type.getName() + ", " + dimensionCount;
  }
}
