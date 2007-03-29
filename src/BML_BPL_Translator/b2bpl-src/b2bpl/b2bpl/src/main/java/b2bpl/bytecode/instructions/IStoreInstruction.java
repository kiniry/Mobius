package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.Opcodes;


public class IStoreInstruction extends LocalVariableInstruction {

  public static final IStoreInstruction ISTORE_0 =
    new IStoreInstruction(Opcodes.ISTORE_0, 0);

  public static final IStoreInstruction ISTORE_1 =
    new IStoreInstruction(Opcodes.ISTORE_1, 1);

  public static final IStoreInstruction ISTORE_2 =
    new IStoreInstruction(Opcodes.ISTORE_2, 2);

  public static final IStoreInstruction ISTORE_3 =
    new IStoreInstruction(Opcodes.ISTORE_3, 3);

  public IStoreInstruction(int index) {
    this(Opcodes.ISTORE, index);
  }

  private IStoreInstruction(int opcode, int index) {
    super(opcode, index);
  }

  public static IStoreInstruction createOptimal(int index) {
    switch (index) {
      case 0:
        return IStoreInstruction.ISTORE_0;
      case 1:
        return IStoreInstruction.ISTORE_1;
      case 2:
        return IStoreInstruction.ISTORE_2;
      case 3:
        return IStoreInstruction.ISTORE_3;
      default:
        return new IStoreInstruction(index);
    }
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitIStoreInstruction(this);
  }

  public String toString() {
    if (opcode == Opcodes.ISTORE) {
      return Opcodes.NAMES[opcode] + " " + index;
    }
    return Opcodes.NAMES[opcode];
  }
}
