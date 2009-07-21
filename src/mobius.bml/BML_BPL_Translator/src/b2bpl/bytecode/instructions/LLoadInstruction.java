package b2bpl.bytecode.instructions;

import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.IOpCodes;


public class LLoadInstruction extends LocalVariableInstruction {

  public static final LLoadInstruction LLOAD_0 =
    new LLoadInstruction(IOpCodes.LLOAD_0, 0);

  public static final LLoadInstruction LLOAD_1 =
    new LLoadInstruction(IOpCodes.LLOAD_1, 1);

  public static final LLoadInstruction LLOAD_2 =
    new LLoadInstruction(IOpCodes.LLOAD_2, 2);

  public static final LLoadInstruction LLOAD_3 =
    new LLoadInstruction(IOpCodes.LLOAD_3, 3);

  public LLoadInstruction(int index) {
    this(IOpCodes.LLOAD, index);
  }

  private LLoadInstruction(int opcode, int index) {
    super(opcode, index);
  }

  public static LLoadInstruction createOptimal(int index) {
    switch (index) {
      case 0:
        return LLoadInstruction.LLOAD_0;
      case 1:
        return LLoadInstruction.LLOAD_1;
      case 2:
        return LLoadInstruction.LLOAD_2;
      case 3:
        return LLoadInstruction.LLOAD_3;
      default:
        return new LLoadInstruction(index);
    }
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitLLoadInstruction(this);
  }

  public String toString() {
    if (opcode == IOpCodes.LLOAD) {
      return IOpCodes.NAMES[opcode] + " " + index;
    }
    return IOpCodes.NAMES[opcode];
  }
}
