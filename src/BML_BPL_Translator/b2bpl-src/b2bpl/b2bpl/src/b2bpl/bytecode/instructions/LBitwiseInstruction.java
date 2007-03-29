package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.Opcodes;


public class LBitwiseInstruction extends ArithmeticInstruction {

  public static final LBitwiseInstruction LSHL =
    new LBitwiseInstruction(Opcodes.LSHL);

  public static final LBitwiseInstruction LSHR =
    new LBitwiseInstruction(Opcodes.LSHR);

  public static final LBitwiseInstruction LUSHR =
    new LBitwiseInstruction(Opcodes.LUSHR);

  public static final LBitwiseInstruction LAND =
    new LBitwiseInstruction(Opcodes.LAND);

  public static final LBitwiseInstruction LOR =
    new LBitwiseInstruction(Opcodes.LOR);

  public static final LBitwiseInstruction LXOR =
    new LBitwiseInstruction(Opcodes.LXOR);

  private LBitwiseInstruction(int opcode) {
    super(opcode);
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitLBitwiseInstruction(this);
  }

  public String toString() {
    return Opcodes.NAMES[opcode];
  }
}
