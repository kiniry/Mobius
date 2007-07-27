package b2bpl.bytecode.instructions;

import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.JReferenceType;
import b2bpl.bytecode.IOpCodes;


public class CheckCastInstruction extends Instruction {

  private static final String[] RUNTIME_EXCEPTIONS = new String[] {
    "java.lang.ClassCastException"
  };

  private final JReferenceType type;

  public CheckCastInstruction(JReferenceType type) {
    super(IOpCodes.CHECKCAST);
    this.type = type;
  }

  public JReferenceType getType() {
    return type;
  }

  public String[] getRuntimeExceptions() {
    return RUNTIME_EXCEPTIONS;
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitCheckCastInstruction(this);
  }

  public String toString() {
    return IOpCodes.NAMES[opcode] + " " + type.getName();
  }
}
