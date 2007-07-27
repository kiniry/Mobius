package b2bpl.bytecode.bml.ast;

import b2bpl.bytecode.BCField;
import b2bpl.bytecode.JReferenceType;
import b2bpl.bytecode.JType;
import b2bpl.bytecode.bml.IBMLExpressionVisitor;


public class BMLFieldExpression extends BMLExpression {

  private final JReferenceType fieldOwner;

  private final String fieldName;

  private final JType fieldType;

  private final String fieldDescriptor;

  private final boolean isGhostField;

  private BCField field;

  public BMLFieldExpression(JReferenceType owner, String name, JType type) {
    this(owner, name, type, false);
  }

  public BMLFieldExpression(
      JReferenceType owner,
      String name,
      JType type,
      boolean isGhostField) {
    this.fieldOwner = owner;
    this.fieldName = name;
    this.fieldType = type;
    this.fieldDescriptor = type.getDescriptor();
    this.isGhostField = isGhostField;
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

  public boolean isGhostField() {
    return isGhostField;
  }

  public BCField getField() {
    return field;
  }

  public void setField(BCField field) {
    this.field = field;
  }

  public <R> R accept(IBMLExpressionVisitor<R> visitor) {
    return visitor.visitFieldExpression(this);
  }

  public String toString() {
    return fieldName;
  }
}
