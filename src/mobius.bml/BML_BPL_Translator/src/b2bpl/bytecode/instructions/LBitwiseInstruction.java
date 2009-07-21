package b2bpl.bytecode.instructions;

import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.IOpCodes;


public class LBitwiseInstruction extends ArithmeticInstruction {

  public static final LBitwiseInstruction LSHL =
    new LBitwiseInstruction(IOpCodes.LSHL);

  public static final LBitwiseInstruction LSHR =
    new LBitwiseInstruction(IOpCodes.LSHR);

  public static final LBitwiseInstruction LUSHR =
    new LBitwiseInstruction(IOpCodes.LUSHR);

  public static final LBitwiseInstruction LAND =
    new LBitwiseInstruction(IOpCodes.LAND);

  public static final LBitwiseInstruction LOR =
    new LBitwiseInstruction(IOpCodes.LOR);

  public static final LBitwiseInstruction LXOR =
    new LBitwiseInstruction(IOpCodes.LXOR);

  private LBitwiseInstruction(int opcode) {
    super(opcode);
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitLBitwiseInstruction(this);
  }

  public String toString() {
    return IOpCodes.NAMES[opcode];
  }
}
