package b2bpl.bytecode.instructions;

import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.JReferenceType;
import b2bpl.bytecode.JType;
import b2bpl.bytecode.IOpCodes;


public class PutFieldInstruction extends FieldInstruction {

  private static final String[] RUNTIME_EXCEPTIONS = new String[] {
    "java.lang.NullPointerException"
  };

  public PutFieldInstruction(
      JReferenceType fieldOwner,
      String fieldName,
      JType fieldType) {
    super(IOpCodes.PUTFIELD, fieldOwner, fieldName, fieldType);
  }

  public String[] getRuntimeExceptions() {
    return RUNTIME_EXCEPTIONS;
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitPutFieldInstruction(this);
  }
}
