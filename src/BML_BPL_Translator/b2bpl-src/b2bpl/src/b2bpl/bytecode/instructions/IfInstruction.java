package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionHandle;
import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.IOpCodes;


public class IfInstruction extends AbstractIfInstruction {

  private IfInstruction(int opcode, InstructionHandle target) {
    super(opcode, target);
  }

  public static IfInstruction createEqual(InstructionHandle target) {
    return new IfInstruction(IOpCodes.IFEQ, target);
  }

  public static IfInstruction createNotEqual(InstructionHandle target) {
    return new IfInstruction(IOpCodes.IFNE, target);
  }

  public static IfInstruction createLower(InstructionHandle target) {
    return new IfInstruction(IOpCodes.IFLT, target);
  }

  public static IfInstruction createGreaterEqual(InstructionHandle target) {
    return new IfInstruction(IOpCodes.IFGE, target);
  }

  public static IfInstruction createGreater(InstructionHandle target) {
    return new IfInstruction(IOpCodes.IFGT, target);
  }

  public static IfInstruction createLowerEqual(InstructionHandle target) {
    return new IfInstruction(IOpCodes.IFLE, target);
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitIfInstruction(this);
  }
}
