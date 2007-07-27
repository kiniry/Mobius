package b2bpl.bytecode.instructions;

import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.IOpCodes;


public class LStoreInstruction extends LocalVariableInstruction {

  public static final LStoreInstruction LSTORE_0 =
    new LStoreInstruction(IOpCodes.LSTORE_0, 0);

  public static final LStoreInstruction LSTORE_1 =
    new LStoreInstruction(IOpCodes.LSTORE_1, 1);

  public static final LStoreInstruction LSTORE_2 =
    new LStoreInstruction(IOpCodes.LSTORE_2, 2);

  public static final LStoreInstruction LSTORE_3 =
    new LStoreInstruction(IOpCodes.LSTORE_3, 3);

  public LStoreInstruction(int index) {
    this(IOpCodes.LSTORE, index);
  }

  private LStoreInstruction(int opcode, int index) {
    super(opcode, index);
  }

  public static LStoreInstruction createOptimal(int index) {
    switch (index) {
      case 0:
        return LStoreInstruction.LSTORE_0;
      case 1:
        return LStoreInstruction.LSTORE_1;
      case 2:
        return LStoreInstruction.LSTORE_2;
      case 3:
        return LStoreInstruction.LSTORE_3;
      default:
        return new LStoreInstruction(index);
    }
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitLStoreInstruction(this);
  }

  public String toString() {
    if (opcode == IOpCodes.LSTORE) {
      return IOpCodes.NAMES[opcode] + " " + index;
    }
    return IOpCodes.NAMES[opcode];
  }
}
