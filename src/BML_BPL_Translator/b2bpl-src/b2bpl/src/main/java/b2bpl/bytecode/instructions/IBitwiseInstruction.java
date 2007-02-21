package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.Opcodes;


public class IBitwiseInstruction extends ArithmeticInstruction {

  public static final IBitwiseInstruction ISHL =
    new IBitwiseInstruction(Opcodes.ISHL);

  public static final IBitwiseInstruction ISHR =
    new IBitwiseInstruction(Opcodes.ISHR);

  public static final IBitwiseInstruction IUSHR =
    new IBitwiseInstruction(Opcodes.IUSHR);

  public static final IBitwiseInstruction IAND =
    new IBitwiseInstruction(Opcodes.IAND);

  public static final IBitwiseInstruction IOR =
    new IBitwiseInstruction(Opcodes.IOR);

  public static final IBitwiseInstruction IXOR =
    new IBitwiseInstruction(Opcodes.IXOR);

  private IBitwiseInstruction(int opcode) {
    super(opcode);
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitIBitwiseInstruction(this);
  }

  public String toString() {
    return Opcodes.NAMES[opcode];
  }
}
