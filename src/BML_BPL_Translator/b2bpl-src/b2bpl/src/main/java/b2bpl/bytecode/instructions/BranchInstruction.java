package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionHandle;
import b2bpl.bytecode.Opcodes;


public abstract class BranchInstruction extends Instruction {

  protected final InstructionHandle target;

  public BranchInstruction(int opcode, InstructionHandle target) {
    super(opcode);
    this.target = target;
  }

  public InstructionHandle getTarget() {
    return target;
  }

  public String toString() {
    return Opcodes.NAMES[opcode] + " " + target.getIndex();
  }
}
