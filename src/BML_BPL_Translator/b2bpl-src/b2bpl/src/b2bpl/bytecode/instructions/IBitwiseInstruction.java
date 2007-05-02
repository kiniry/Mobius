package b2bpl.bytecode.instructions;

import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.IOpCodes;


public class IBitwiseInstruction extends ArithmeticInstruction {

  public static final IBitwiseInstruction ISHL =
    new IBitwiseInstruction(IOpCodes.ISHL);

  public static final IBitwiseInstruction ISHR =
    new IBitwiseInstruction(IOpCodes.ISHR);

  public static final IBitwiseInstruction IUSHR =
    new IBitwiseInstruction(IOpCodes.IUSHR);

  public static final IBitwiseInstruction IAND =
    new IBitwiseInstruction(IOpCodes.IAND);

  public static final IBitwiseInstruction IOR =
    new IBitwiseInstruction(IOpCodes.IOR);

  public static final IBitwiseInstruction IXOR =
    new IBitwiseInstruction(IOpCodes.IXOR);

  private IBitwiseInstruction(int opcode) {
    super(opcode);
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitIBitwiseInstruction(this);
  }

  public String toString() {
    return IOpCodes.NAMES[opcode];
  }
}
