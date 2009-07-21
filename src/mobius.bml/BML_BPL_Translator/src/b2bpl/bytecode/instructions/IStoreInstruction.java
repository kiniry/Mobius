package b2bpl.bytecode.instructions;

import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.IOpCodes;


public class IStoreInstruction extends LocalVariableInstruction {

  public static final IStoreInstruction ISTORE_0 =
    new IStoreInstruction(IOpCodes.ISTORE_0, 0);

  public static final IStoreInstruction ISTORE_1 =
    new IStoreInstruction(IOpCodes.ISTORE_1, 1);

  public static final IStoreInstruction ISTORE_2 =
    new IStoreInstruction(IOpCodes.ISTORE_2, 2);

  public static final IStoreInstruction ISTORE_3 =
    new IStoreInstruction(IOpCodes.ISTORE_3, 3);

  public IStoreInstruction(int index) {
    this(IOpCodes.ISTORE, index);
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

  public void accept(IInstructionVisitor visitor) {
    visitor.visitIStoreInstruction(this);
  }

  public String toString() {
    if (opcode == IOpCodes.ISTORE) {
      return IOpCodes.NAMES[opcode] + " " + index;
    }
    return IOpCodes.NAMES[opcode];
  }
}
