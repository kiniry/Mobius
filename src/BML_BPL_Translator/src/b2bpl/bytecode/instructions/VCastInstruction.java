package b2bpl.bytecode.instructions;

import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.JBaseType;
import b2bpl.bytecode.IOpCodes;


public class VCastInstruction extends Instruction {

  public static final VCastInstruction I2S =
    new VCastInstruction(IOpCodes.I2S, JBaseType.INT, JBaseType.SHORT);

  public static final VCastInstruction I2B =
    new VCastInstruction(IOpCodes.I2B, JBaseType.INT, JBaseType.BYTE);

  public static final VCastInstruction I2C =
    new VCastInstruction(IOpCodes.I2C, JBaseType.INT, JBaseType.CHAR);

  public static final VCastInstruction I2L =
    new VCastInstruction(IOpCodes.I2L, JBaseType.INT, JBaseType.LONG);

  public static final VCastInstruction L2I =
    new VCastInstruction(IOpCodes.L2I, JBaseType.LONG, JBaseType.INT);

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

  public void accept(IInstructionVisitor visitor) {
    visitor.visitVCastInstruction(this);
  }

  public String toString() {
    return IOpCodes.NAMES[opcode];
  }
}
