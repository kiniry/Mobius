package b2bpl.bytecode.instructions;

import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.JReferenceType;
import b2bpl.bytecode.IOpCodes;


public class InstanceOfInstruction extends Instruction {

  private final JReferenceType type;

  public InstanceOfInstruction(JReferenceType type) {
    super(IOpCodes.INSTANCEOF);
    this.type = type;
  }

  public JReferenceType getType() {
    return type;
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitInstanceOfInstruction(this);
  }

  public String toString() {
    return IOpCodes.NAMES[opcode] + " " + type.getName();
  }
}
