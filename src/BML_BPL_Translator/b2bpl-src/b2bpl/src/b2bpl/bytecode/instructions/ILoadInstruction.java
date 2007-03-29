package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.Opcodes;


public class ILoadInstruction extends LocalVariableInstruction {

  public static final ILoadInstruction ILOAD_0 =
    new ILoadInstruction(Opcodes.ILOAD_0, 0);

  public static final ILoadInstruction ILOAD_1 =
    new ILoadInstruction(Opcodes.ILOAD_1, 1);

  public static final ILoadInstruction ILOAD_2 =
    new ILoadInstruction(Opcodes.ILOAD_2, 2);

  public static final ILoadInstruction ILOAD_3 =
    new ILoadInstruction(Opcodes.ILOAD_3, 3);

  public ILoadInstruction(int index) {
    this(Opcodes.ILOAD, index);
  }

  private ILoadInstruction(int opcode, int index) {
    super(opcode, index);
  }

  public static ILoadInstruction createOptimal(int index) {
    switch (index) {
      case 0:
        return ILoadInstruction.ILOAD_0;
      case 1:
        return ILoadInstruction.ILOAD_1;
      case 2:
        return ILoadInstruction.ILOAD_2;
      case 3:
        return ILoadInstruction.ILOAD_3;
      default:
        return new ILoadInstruction(index);
    }
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitILoadInstruction(this);
  }

  public String toString() {
    if (opcode == Opcodes.ILOAD) {
      return Opcodes.NAMES[opcode] + " " + index;
    }
    return Opcodes.NAMES[opcode];
  }
}
