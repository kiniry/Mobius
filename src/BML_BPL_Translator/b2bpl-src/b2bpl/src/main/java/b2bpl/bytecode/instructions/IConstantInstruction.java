package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.Opcodes;


public class IConstantInstruction extends Instruction {

  public static final IConstantInstruction ICONST_M1 =
    new IConstantInstruction(Opcodes.ICONST_M1, -1);

  public static final IConstantInstruction ICONST_0 =
    new IConstantInstruction(Opcodes.ICONST_0, 0);

  public static final IConstantInstruction ICONST_1 =
    new IConstantInstruction(Opcodes.ICONST_1, 1);

  public static final IConstantInstruction ICONST_2 =
    new IConstantInstruction(Opcodes.ICONST_2, 2);

  public static final IConstantInstruction ICONST_3 =
    new IConstantInstruction(Opcodes.ICONST_3, 3);

  public static final IConstantInstruction ICONST_4 =
    new IConstantInstruction(Opcodes.ICONST_4, 4);

  public static final IConstantInstruction ICONST_5 =
    new IConstantInstruction(Opcodes.ICONST_5, 5);

  private final int constant;

  public IConstantInstruction(int constant) {
    this(
        ((Byte.MIN_VALUE <= constant) && (constant <= Byte.MAX_VALUE)) ?
              Opcodes.BIPUSH : Opcodes.SIPUSH,
        constant);
  }

  private IConstantInstruction(int opcode, int constant) {
    super(opcode);
    this.constant = constant;
  }

  public static IConstantInstruction createOptimal(int constant) {
    switch (constant) {
      case -1:
        return IConstantInstruction.ICONST_M1;
      case 0:
        return IConstantInstruction.ICONST_0;
      case 1:
        return IConstantInstruction.ICONST_1;
      case 2:
        return IConstantInstruction.ICONST_2;
      case 3:
        return IConstantInstruction.ICONST_3;
      case 4:
        return IConstantInstruction.ICONST_4;
      case 5:
        return IConstantInstruction.ICONST_5;
      default:
        return new IConstantInstruction(constant);
    }
  }

  public int getConstant() {
    return constant;
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitIConstantInstruction(this);
  }

  public String toString() {
    if ((opcode == Opcodes.BIPUSH) || (opcode == Opcodes.SIPUSH)) {
      return Opcodes.NAMES[opcode] + " " + constant;
    }
    return Opcodes.NAMES[opcode];
  }
}
