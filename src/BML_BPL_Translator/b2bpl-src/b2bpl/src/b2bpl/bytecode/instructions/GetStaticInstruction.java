package b2bpl.bytecode.instructions;

import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.JReferenceType;
import b2bpl.bytecode.JType;
import b2bpl.bytecode.IOpCodes;


public class GetStaticInstruction extends FieldInstruction {

  public GetStaticInstruction(
      JReferenceType fieldOwner,
      String fieldName,
      JType fieldType) {
    super(IOpCodes.GETSTATIC, fieldOwner, fieldName, fieldType);
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitGetStaticInstruction(this);
  }
}
