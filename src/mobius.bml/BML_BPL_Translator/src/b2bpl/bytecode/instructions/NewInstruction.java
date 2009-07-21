package b2bpl.bytecode.instructions;

import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.JReferenceType;
import b2bpl.bytecode.IOpCodes;


public class NewInstruction extends Instruction {

  private final JReferenceType type;

  public NewInstruction(JReferenceType type) {
    super(IOpCodes.NEW);
    this.type = type;
  }

  public JReferenceType getType() {
    return type;
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitNewInstruction(this);
  }

  public String toString() {
    return IOpCodes.NAMES[opcode] + " " + type.getName();
  }
}
