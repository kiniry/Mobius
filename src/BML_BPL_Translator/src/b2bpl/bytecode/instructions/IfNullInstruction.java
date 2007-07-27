package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionHandle;
import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.IOpCodes;


public class IfNullInstruction extends AbstractIfInstruction {

  public IfNullInstruction(InstructionHandle target) {
    super(IOpCodes.IFNULL, target);
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitIfNullInstruction(this);
  }
}
