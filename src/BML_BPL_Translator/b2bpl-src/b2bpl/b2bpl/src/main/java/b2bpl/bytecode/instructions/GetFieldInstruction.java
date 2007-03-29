package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.JReferenceType;
import b2bpl.bytecode.JType;
import b2bpl.bytecode.Opcodes;


public class GetFieldInstruction extends FieldInstruction {

  private static final String[] RUNTIME_EXCEPTIONS = new String[] {
    "java.lang.NullPointerException"
  };

  public GetFieldInstruction(
      JReferenceType fieldOwner,
      String fieldName,
      JType fieldType) {
    super(Opcodes.GETFIELD, fieldOwner, fieldName, fieldType);
  }

  public String[] getRuntimeExceptions() {
    return RUNTIME_EXCEPTIONS;
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitGetFieldInstruction(this);
  }
}
