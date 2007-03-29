package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.JBaseType;
import b2bpl.bytecode.Opcodes;


public class NewArrayInstruction extends Instruction {

  private static final String[] RUNTIME_EXCEPTIONS = new String[] {
    "java.lang.NegativeArraySizeException"
  };

  private final JBaseType type;

  public NewArrayInstruction(JBaseType type) {
    super(Opcodes.NEWARRAY);
    this.type = type;
  }

  public JBaseType getType() {
    return type;
  }

  public String[] getRuntimeExceptions() {
    return RUNTIME_EXCEPTIONS;
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitNewArrayInstruction(this);
  }

  public String toString() {
    return Opcodes.NAMES[opcode] + " " + type.getName();
  }
}
