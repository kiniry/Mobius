package b2bpl.bytecode.instructions;

import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.IOpCodes;


public class LdcInstruction extends Instruction {

  private final Object constant;

  public LdcInstruction(Object constant) {
    super(((constant instanceof Long) || (constant instanceof Double)) ?
            IOpCodes.LDC2_W : IOpCodes.LDC);
    this.constant = constant;
  }

  public Object getConstant() {
    return constant;
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitLdcInstruction(this);
  }

  public String toString() {
    StringBuffer sb = new StringBuffer();

    sb.append(IOpCodes.NAMES[opcode]).append(" ");
    if (constant instanceof String) {
      sb.append('"').append(constant).append('"');
    } else {
      sb.append(constant);
    }

    return sb.toString();
  }
}
