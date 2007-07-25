package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionHandle;


public abstract class AbstractIfInstruction extends BranchInstruction {

  public AbstractIfInstruction(int opcode, InstructionHandle target) {
    super(opcode, target);
  }
}
