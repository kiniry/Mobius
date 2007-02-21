package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.JReferenceType;
import b2bpl.bytecode.Opcodes;


public class CheckCastInstruction extends Instruction {

  private static final String[] RUNTIME_EXCEPTIONS = new String[] {
    "java.lang.ClassCastException"
  };

  private final JReferenceType type;

  public CheckCastInstruction(JReferenceType type) {
    super(Opcodes.CHECKCAST);
    this.type = type;
  }

  public JReferenceType getType() {
    return type;
  }

  public String[] getRuntimeExceptions() {
    return RUNTIME_EXCEPTIONS;
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitCheckCastInstruction(this);
  }

  public String toString() {
    return Opcodes.NAMES[opcode] + " " + type.getName();
  }
}
