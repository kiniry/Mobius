package b2bpl.bytecode.instructions;

import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.JReferenceType;
import b2bpl.bytecode.IOpCodes;


public class ANewArrayInstruction extends Instruction {

  private static final String[] RUNTIME_EXCEPTIONS = new String[] {
    "java.lang.NegativeArraySizeException"
  };

  private final JReferenceType type;

  public ANewArrayInstruction(JReferenceType type) {
    super(IOpCodes.ANEWARRAY);
    this.type = type;
  }

  public JReferenceType getType() {
    return type;
  }

  public String[] getRuntimeExceptions() {
    return RUNTIME_EXCEPTIONS;
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitANewArrayInstruction(this);
  }

  public String toString() {
    return IOpCodes.NAMES[opcode] + " " + type.getName();
  }
}
