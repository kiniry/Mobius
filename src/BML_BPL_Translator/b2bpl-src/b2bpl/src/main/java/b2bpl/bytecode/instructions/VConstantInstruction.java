package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.Opcodes;


public class VConstantInstruction extends Instruction {

  public static final VConstantInstruction ICONST_M1 =
    new VConstantInstruction(Opcodes.ICONST_M1, -1);

  public static final VConstantInstruction ICONST_0 =
    new VConstantInstruction(Opcodes.ICONST_0, 0);

  public static final VConstantInstruction ICONST_1 =
    new VConstantInstruction(Opcodes.ICONST_1, 1);

  public static final VConstantInstruction ICONST_2 =
    new VConstantInstruction(Opcodes.ICONST_2, 2);

  public static final VConstantInstruction ICONST_3 =
    new VConstantInstruction(Opcodes.ICONST_3, 3);

  public static final VConstantInstruction ICONST_4 =
    new VConstantInstruction(Opcodes.ICONST_4, 4);

  public static final VConstantInstruction ICONST_5 =
    new VConstantInstruction(Opcodes.ICONST_5, 5);

  public static final VConstantInstruction LCONST_0 =
    new VConstantInstruction(Opcodes.LCONST_0, 0);

  public static final VConstantInstruction LCONST_1 =
    new VConstantInstruction(Opcodes.LCONST_1, 1);

  private final int constant;

  public VConstantInstruction(int constant) {
    this(
        ((Byte.MIN_VALUE <= constant) && (constant <= Byte.MAX_VALUE)) ?
              Opcodes.BIPUSH : Opcodes.SIPUSH,
        constant);
  }

  private VConstantInstruction(int opcode, int constant) {
    super(opcode);
    this.constant = constant;
  }

  public static VConstantInstruction createIConstant(int constant) {
    switch (constant) {
      case -1:
        return VConstantInstruction.ICONST_M1;
      case 0:
        return VConstantInstruction.ICONST_0;
      case 1:
        return VConstantInstruction.ICONST_1;
      case 2:
        return VConstantInstruction.ICONST_2;
      case 3:
        return VConstantInstruction.ICONST_3;
      case 4:
        return VConstantInstruction.ICONST_4;
      case 5:
        return VConstantInstruction.ICONST_5;
      default:
        return new VConstantInstruction(constant);
    }
  }

  public int getConstant() {
    return constant;
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitVConstantInstruction(this);
  }

  public String toString() {
    if ((opcode == Opcodes.BIPUSH) || (opcode == Opcodes.SIPUSH)) {
      return Opcodes.NAMES[opcode] + " " + constant;
    }
    return Opcodes.NAMES[opcode];
  }
}
