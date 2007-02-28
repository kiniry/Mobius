package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.JReferenceType;
import b2bpl.bytecode.Opcodes;


public class ANewArrayInstruction extends Instruction {

  private static final String[] RUNTIME_EXCEPTIONS = new String[] {
    "java.lang.NegativeArraySizeException"
  };

  private final JReferenceType type;

  public ANewArrayInstruction(JReferenceType type) {
    super(Opcodes.ANEWARRAY);
    this.type = type;
  }

  public JReferenceType getType() {
    return type;
  }

  public String[] getRuntimeExceptions() {
    return RUNTIME_EXCEPTIONS;
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitANewArrayInstruction(this);
  }

  public String toString() {
    return Opcodes.NAMES[opcode] + " " + type.getName();
  }
}
