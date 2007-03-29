package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.JArrayType;
import b2bpl.bytecode.Opcodes;


public class MultiANewArrayInstruction extends Instruction {

  private static final String[] RUNTIME_EXCEPTIONS = new String[] {
    "java.lang.NegativeArraySizeException"
  };

  private final JArrayType type;

  private final int dimensionCount;

  public MultiANewArrayInstruction(JArrayType type, int dimensionCount) {
    super(Opcodes.MULTIANEWARRAY);
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

  public void accept(InstructionVisitor visitor) {
    visitor.visitMultiANewArrayInstruction(this);
  }

  public String toString() {
    return Opcodes.NAMES[opcode] + " " + type.getName() + ", " + dimensionCount;
  }
}
