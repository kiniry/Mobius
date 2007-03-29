package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionHandle;
import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.Opcodes;


public class IfInstruction extends AbstractIfInstruction {

  private IfInstruction(int opcode, InstructionHandle target) {
    super(opcode, target);
  }

  public static IfInstruction createEqual(InstructionHandle target) {
    return new IfInstruction(Opcodes.IFEQ, target);
  }

  public static IfInstruction createNotEqual(InstructionHandle target) {
    return new IfInstruction(Opcodes.IFNE, target);
  }

  public static IfInstruction createLower(InstructionHandle target) {
    return new IfInstruction(Opcodes.IFLT, target);
  }

  public static IfInstruction createGreaterEqual(InstructionHandle target) {
    return new IfInstruction(Opcodes.IFGE, target);
  }

  public static IfInstruction createGreater(InstructionHandle target) {
    return new IfInstruction(Opcodes.IFGT, target);
  }

  public static IfInstruction createLowerEqual(InstructionHandle target) {
    return new IfInstruction(Opcodes.IFLE, target);
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitIfInstruction(this);
  }
}
