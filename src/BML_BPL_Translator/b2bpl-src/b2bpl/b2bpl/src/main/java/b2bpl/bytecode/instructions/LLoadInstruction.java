package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.Opcodes;


public class LLoadInstruction extends LocalVariableInstruction {

  public static final LLoadInstruction LLOAD_0 =
    new LLoadInstruction(Opcodes.LLOAD_0, 0);

  public static final LLoadInstruction LLOAD_1 =
    new LLoadInstruction(Opcodes.LLOAD_1, 1);

  public static final LLoadInstruction LLOAD_2 =
    new LLoadInstruction(Opcodes.LLOAD_2, 2);

  public static final LLoadInstruction LLOAD_3 =
    new LLoadInstruction(Opcodes.LLOAD_3, 3);

  public LLoadInstruction(int index) {
    this(Opcodes.LLOAD, index);
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

  public void accept(InstructionVisitor visitor) {
    visitor.visitLLoadInstruction(this);
  }

  public String toString() {
    if (opcode == Opcodes.LLOAD) {
      return Opcodes.NAMES[opcode] + " " + index;
    }
    return Opcodes.NAMES[opcode];
  }
}
