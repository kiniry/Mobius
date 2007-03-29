package b2bpl.bytecode.instructions;

import b2bpl.bytecode.BCField;
import b2bpl.bytecode.JReferenceType;
import b2bpl.bytecode.JType;
import b2bpl.bytecode.Opcodes;


public abstract class FieldInstruction extends Instruction {

  protected final JReferenceType fieldOwner;

  protected final String fieldName;

  protected final JType fieldType;

  protected final String fieldDescriptor;

  protected BCField field;

  public FieldInstruction(
      int opcode,
      JReferenceType fieldOwner,
      String fieldName,
      JType fieldType) {
    super(opcode);
    this.fieldOwner = fieldOwner;
    this.fieldName = fieldName;
    this.fieldType = fieldType;
    this.fieldDescriptor = fieldType.getDescriptor();
  }

  public JReferenceType getFieldOwner() {
    return fieldOwner;
  }

  public String getFieldName() {
    return fieldName;
  }

  public JType getFieldType() {
    return fieldType;
  }

  public String getFieldDescriptor() {
    return fieldDescriptor;
  }

  public BCField getField() {
    return field;
  }

  public void setField(BCField field) {
    this.field = field;
  }

  public String toString() {
    StringBuffer sb = new StringBuffer();

    sb.append(Opcodes.NAMES[opcode]);
    sb.append(' ');
    sb.append(fieldOwner.getName());
    sb.append('.');
    sb.append(fieldName);
    sb.append(" : ");
    sb.append(fieldType.getName());

    return sb.toString();
  }
}
