package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionHandle;
import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.Opcodes;


public class IfNonNullInstruction extends AbstractIfInstruction {

  public IfNonNullInstruction(InstructionHandle target) {
    super(Opcodes.IFNONNULL, target);
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitIfNonNullInstruction(this);
  }
}
