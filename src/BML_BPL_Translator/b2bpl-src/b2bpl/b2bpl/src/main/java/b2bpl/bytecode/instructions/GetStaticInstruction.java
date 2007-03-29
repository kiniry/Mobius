package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.JReferenceType;
import b2bpl.bytecode.JType;
import b2bpl.bytecode.Opcodes;


public class GetStaticInstruction extends FieldInstruction {

  public GetStaticInstruction(
      JReferenceType fieldOwner,
      String fieldName,
      JType fieldType) {
    super(Opcodes.GETSTATIC, fieldOwner, fieldName, fieldType);
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitGetStaticInstruction(this);
  }
}
