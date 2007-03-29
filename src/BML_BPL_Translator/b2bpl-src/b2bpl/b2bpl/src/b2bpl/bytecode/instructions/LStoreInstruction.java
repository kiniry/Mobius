package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.Opcodes;


public class LStoreInstruction extends LocalVariableInstruction {

  public static final LStoreInstruction LSTORE_0 =
    new LStoreInstruction(Opcodes.LSTORE_0, 0);

  public static final LStoreInstruction LSTORE_1 =
    new LStoreInstruction(Opcodes.LSTORE_1, 1);

  public static final LStoreInstruction LSTORE_2 =
    new LStoreInstruction(Opcodes.LSTORE_2, 2);

  public static final LStoreInstruction LSTORE_3 =
    new LStoreInstruction(Opcodes.LSTORE_3, 3);

  public LStoreInstruction(int index) {
    this(Opcodes.LSTORE, index);
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

  public void accept(InstructionVisitor visitor) {
    visitor.visitLStoreInstruction(this);
  }

  public String toString() {
    if (opcode == Opcodes.LSTORE) {
      return Opcodes.NAMES[opcode] + " " + index;
    }
    return Opcodes.NAMES[opcode];
  }
}
