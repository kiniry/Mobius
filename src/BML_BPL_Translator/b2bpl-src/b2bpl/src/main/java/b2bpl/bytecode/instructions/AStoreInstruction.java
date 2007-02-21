package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.Opcodes;


public class AStoreInstruction extends LocalVariableInstruction {

  public static final AStoreInstruction ASTORE_0 =
    new AStoreInstruction(Opcodes.ASTORE_0, 0);

  public static final AStoreInstruction ASTORE_1 =
    new AStoreInstruction(Opcodes.ASTORE_1, 1);

  public static final AStoreInstruction ASTORE_2 =
    new AStoreInstruction(Opcodes.ASTORE_2, 2);

  public static final AStoreInstruction ASTORE_3 =
    new AStoreInstruction(Opcodes.ASTORE_3, 3);

  public AStoreInstruction(int index) {
    this(Opcodes.ASTORE, index);
  }

  private AStoreInstruction(int opcode, int index) {
    super(opcode, index);
  }

  public static AStoreInstruction createOptimal(int index) {
    switch (index) {
      case 0:
        return AStoreInstruction.ASTORE_0;
      case 1:
        return AStoreInstruction.ASTORE_1;
      case 2:
        return AStoreInstruction.ASTORE_2;
      case 3:
        return AStoreInstruction.ASTORE_3;
      default:
        return new AStoreInstruction(index);
    }
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitAStoreInstruction(this);
  }

  public String toString() {
    if (opcode == Opcodes.ASTORE) {
      return Opcodes.NAMES[opcode] + " " + index;
    }
    return Opcodes.NAMES[opcode];
  }
}
