package b2bpl.bytecode.instructions;

import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.JReferenceType;
import b2bpl.bytecode.JType;
import b2bpl.bytecode.IOpCodes;


public class PutStaticInstruction extends FieldInstruction {

  public PutStaticInstruction(
      JReferenceType fieldOwner,
      String fieldName,
      JType fieldType) {
    super(IOpCodes.PUTSTATIC, fieldOwner, fieldName, fieldType);
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitPutStaticInstruction(this);
  }
}
