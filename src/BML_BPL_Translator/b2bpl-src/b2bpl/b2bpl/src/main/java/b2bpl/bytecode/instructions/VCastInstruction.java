package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.JBaseType;
import b2bpl.bytecode.Opcodes;


public class VCastInstruction extends Instruction {

  public static final VCastInstruction I2S =
    new VCastInstruction(Opcodes.I2S, JBaseType.INT, JBaseType.SHORT);

  public static final VCastInstruction I2B =
    new VCastInstruction(Opcodes.I2B, JBaseType.INT, JBaseType.BYTE);

  public static final VCastInstruction I2C =
    new VCastInstruction(Opcodes.I2C, JBaseType.INT, JBaseType.CHAR);

  public static final VCastInstruction I2L =
    new VCastInstruction(Opcodes.I2L, JBaseType.INT, JBaseType.LONG);

  public static final VCastInstruction L2I =
    new VCastInstruction(Opcodes.L2I, JBaseType.LONG, JBaseType.INT);

  private final JBaseType sourceType;

  private final JBaseType targetType;

  private VCastInstruction(
      int opcode,
      JBaseType sourceType,
      JBaseType targetType) {
    super(opcode);
    this.sourceType = sourceType;
    this.targetType = targetType;
  }

  public JBaseType getSourceType() {
    return sourceType;
  }

  public JBaseType getTargetType() {
    return targetType;
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitVCastInstruction(this);
  }

  public String toString() {
    return Opcodes.NAMES[opcode];
  }
}
