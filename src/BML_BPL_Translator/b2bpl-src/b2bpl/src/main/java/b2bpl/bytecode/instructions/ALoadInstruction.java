package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.Opcodes;


public class ALoadInstruction extends LocalVariableInstruction {

  public static final ALoadInstruction ALOAD_0 =
    new ALoadInstruction(Opcodes.ALOAD_0, 0);

  public static final ALoadInstruction ALOAD_1 =
    new ALoadInstruction(Opcodes.ALOAD_1, 1);

  public static final ALoadInstruction ALOAD_2 =
    new ALoadInstruction(Opcodes.ALOAD_2, 2);

  public static final ALoadInstruction ALOAD_3 =
    new ALoadInstruction(Opcodes.ALOAD_3, 3);

  public ALoadInstruction(int index) {
    this(Opcodes.ALOAD, index);
  }

  private ALoadInstruction(int opcode, int index) {
    super(opcode, index);
  }

  public static ALoadInstruction createOptimal(int index) {
    switch (index) {
      case 0:
        return ALoadInstruction.ALOAD_0;
      case 1:
        return ALoadInstruction.ALOAD_1;
      case 2:
        return ALoadInstruction.ALOAD_2;
      case 3:
        return ALoadInstruction.ALOAD_3;
      default:
        return new ALoadInstruction(index);
    }
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitALoadInstruction(this);
  }

  public String toString() {
    if (opcode == Opcodes.ALOAD) {
      return Opcodes.NAMES[opcode] + " " + index;
    }
    return Opcodes.NAMES[opcode];
  }
}
