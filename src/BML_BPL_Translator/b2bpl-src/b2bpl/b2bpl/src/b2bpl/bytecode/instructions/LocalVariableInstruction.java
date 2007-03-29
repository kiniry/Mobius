package b2bpl.bytecode.instructions;


public abstract class LocalVariableInstruction extends Instruction {

  protected final int index;

  public LocalVariableInstruction(int opcode, int index) {
    super(opcode);
    this.index = index;
  }

  public int getIndex() {
    return index;
  }
}
