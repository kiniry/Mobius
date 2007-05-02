package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionHandle;
import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.IOpCodes;


public class IfACmpInstruction extends AbstractIfInstruction {

  private IfACmpInstruction(int opcode, InstructionHandle target) {
    super(opcode, target);
  }

  public static IfACmpInstruction createEqual(InstructionHandle target) {
    return new IfACmpInstruction(IOpCodes.IF_ACMPEQ, target);
  }

  public static IfACmpInstruction createNotEqual(InstructionHandle target) {
    return new IfACmpInstruction(IOpCodes.IF_ACMPNE, target);
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitIfACmpInstruction(this);
  }
}
