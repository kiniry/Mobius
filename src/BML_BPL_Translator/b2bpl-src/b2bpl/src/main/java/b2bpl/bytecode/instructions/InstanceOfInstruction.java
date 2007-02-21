package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.JReferenceType;
import b2bpl.bytecode.Opcodes;


public class InstanceOfInstruction extends Instruction {

  private final JReferenceType type;

  public InstanceOfInstruction(JReferenceType type) {
    super(Opcodes.INSTANCEOF);
    this.type = type;
  }

  public JReferenceType getType() {
    return type;
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitInstanceOfInstruction(this);
  }

  public String toString() {
    return Opcodes.NAMES[opcode] + " " + type.getName();
  }
}
