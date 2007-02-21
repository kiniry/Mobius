package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionHandle;
import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.Opcodes;


public class IfNullInstruction extends AbstractIfInstruction {

  public IfNullInstruction(InstructionHandle target) {
    super(Opcodes.IFNULL, target);
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitIfNullInstruction(this);
  }
}
