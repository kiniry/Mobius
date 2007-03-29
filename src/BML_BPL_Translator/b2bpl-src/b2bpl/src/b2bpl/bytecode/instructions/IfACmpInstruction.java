package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionHandle;
import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.Opcodes;


public class IfACmpInstruction extends AbstractIfInstruction {

  private IfACmpInstruction(int opcode, InstructionHandle target) {
    super(opcode, target);
  }

  public static IfACmpInstruction createEqual(InstructionHandle target) {
    return new IfACmpInstruction(Opcodes.IF_ACMPEQ, target);
  }

  public static IfACmpInstruction createNotEqual(InstructionHandle target) {
    return new IfACmpInstruction(Opcodes.IF_ACMPNE, target);
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitIfACmpInstruction(this);
  }
}
