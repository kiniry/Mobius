package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.JReferenceType;
import b2bpl.bytecode.Opcodes;


public class NewInstruction extends Instruction {

  private final JReferenceType type;

  public NewInstruction(JReferenceType type) {
    super(Opcodes.NEW);
    this.type = type;
  }

  public JReferenceType getType() {
    return type;
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitNewInstruction(this);
  }

  public String toString() {
    return Opcodes.NAMES[opcode] + " " + type.getName();
  }
}
