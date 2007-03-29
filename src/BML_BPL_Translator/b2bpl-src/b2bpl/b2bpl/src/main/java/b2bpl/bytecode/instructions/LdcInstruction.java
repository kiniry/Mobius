package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.Opcodes;


public class LdcInstruction extends Instruction {

  private final Object constant;

  public LdcInstruction(Object constant) {
    super(((constant instanceof Long) || (constant instanceof Double)) ?
            Opcodes.LDC2_W : Opcodes.LDC);
    this.constant = constant;
  }

  public Object getConstant() {
    return constant;
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitLdcInstruction(this);
  }

  public String toString() {
    StringBuffer sb = new StringBuffer();

    sb.append(Opcodes.NAMES[opcode]).append(" ");
    if (constant instanceof String) {
      sb.append('"').append(constant).append('"');
    } else {
      sb.append(constant);
    }

    return sb.toString();
  }
}
