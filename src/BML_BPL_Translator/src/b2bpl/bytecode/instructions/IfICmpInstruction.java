package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionHandle;
import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.IOpCodes;


public class IfICmpInstruction extends AbstractIfInstruction {

  private IfICmpInstruction(int opcode, InstructionHandle target) {
    super(opcode, target);
  }

  public static IfICmpInstruction createEqual(InstructionHandle target) {
    return new IfICmpInstruction(IOpCodes.IF_ICMPEQ, target);
  }

  public static IfICmpInstruction createNotEqual(InstructionHandle target) {
    return new IfICmpInstruction(IOpCodes.IF_ICMPNE, target);
  }

  public static IfICmpInstruction createLower(InstructionHandle target) {
    return new IfICmpInstruction(IOpCodes.IF_ICMPLT, target);
  }

  public static IfICmpInstruction createGreaterEqual(InstructionHandle target) {
    return new IfICmpInstruction(IOpCodes.IF_ICMPGE, target);
  }

  public static IfICmpInstruction createGreater(InstructionHandle target) {
    return new IfICmpInstruction(IOpCodes.IF_ICMPGT, target);
  }

  public static IfICmpInstruction createLowerEqual(InstructionHandle target) {
    return new IfICmpInstruction(IOpCodes.IF_ICMPLE, target);
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitIfICmpInstruction(this);
  }
}
