package b2bpl.bytecode.instructions;

import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.JBaseType;
import b2bpl.bytecode.IOpCodes;


public class NewArrayInstruction extends Instruction {

  private static final String[] RUNTIME_EXCEPTIONS = new String[] {
    "java.lang.NegativeArraySizeException"
  };

  private final JBaseType type;

  public NewArrayInstruction(JBaseType type) {
    super(IOpCodes.NEWARRAY);
    this.type = type;
  }

  public JBaseType getType() {
    return type;
  }

  public String[] getRuntimeExceptions() {
    return RUNTIME_EXCEPTIONS;
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitNewArrayInstruction(this);
  }

  public String toString() {
    return IOpCodes.NAMES[opcode] + " " + type.getName();
  }
}
