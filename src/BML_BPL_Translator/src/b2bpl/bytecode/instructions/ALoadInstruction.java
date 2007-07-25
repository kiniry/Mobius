package b2bpl.bytecode.instructions;

import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.IOpCodes;


public class ALoadInstruction extends LocalVariableInstruction {

  public static final ALoadInstruction ALOAD_0 =
    new ALoadInstruction(IOpCodes.ALOAD_0, 0);

  public static final ALoadInstruction ALOAD_1 =
    new ALoadInstruction(IOpCodes.ALOAD_1, 1);

  public static final ALoadInstruction ALOAD_2 =
    new ALoadInstruction(IOpCodes.ALOAD_2, 2);

  public static final ALoadInstruction ALOAD_3 =
    new ALoadInstruction(IOpCodes.ALOAD_3, 3);

  public ALoadInstruction(int index) {
    this(IOpCodes.ALOAD, index);
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

  public void accept(IInstructionVisitor visitor) {
    visitor.visitALoadInstruction(this);
  }

  public String toString() {
    if (opcode == IOpCodes.ALOAD) {
      return IOpCodes.NAMES[opcode] + " " + index;
    }
    return IOpCodes.NAMES[opcode];
  }
}
