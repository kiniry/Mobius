package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionHandle;
import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.Opcodes;


public class IfICmpInstruction extends AbstractIfInstruction {

  private IfICmpInstruction(int opcode, InstructionHandle target) {
    super(opcode, target);
  }

  public static IfICmpInstruction createEqual(InstructionHandle target) {
    return new IfICmpInstruction(Opcodes.IF_ICMPEQ, target);
  }

  public static IfICmpInstruction createNotEqual(InstructionHandle target) {
    return new IfICmpInstruction(Opcodes.IF_ICMPNE, target);
  }

  public static IfICmpInstruction createLower(InstructionHandle target) {
    return new IfICmpInstruction(Opcodes.IF_ICMPLT, target);
  }

  public static IfICmpInstruction createGreaterEqual(InstructionHandle target) {
    return new IfICmpInstruction(Opcodes.IF_ICMPGE, target);
  }

  public static IfICmpInstruction createGreater(InstructionHandle target) {
    return new IfICmpInstruction(Opcodes.IF_ICMPGT, target);
  }

  public static IfICmpInstruction createLowerEqual(InstructionHandle target) {
    return new IfICmpInstruction(Opcodes.IF_ICMPLE, target);
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitIfICmpInstruction(this);
  }
}
