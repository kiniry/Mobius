package b2bpl.bytecode.bml.ast;

import b2bpl.bytecode.BCField;
import b2bpl.bytecode.bml.IBMLExpressionVisitor;


public class BMLFieldAccessExpression extends BMLExpression {

  private final BMLExpression prefix;

  private final BMLFieldExpression fieldReference;

  public BMLFieldAccessExpression(
      BMLExpression prefix,
      BMLFieldExpression fieldReference) {
    this.prefix = prefix;
    this.fieldReference = fieldReference;
  }

  public BMLExpression getPrefix() {
    return prefix;
  }

  public BMLFieldExpression getFieldReference() {
    return fieldReference;
  }

  public BCField getField() {
    return fieldReference.getField();
  }

  public <R> R accept(IBMLExpressionVisitor<R> visitor) {
    return visitor.visitFieldAccessExpression(this);
  }

  public String toString() {
    return prefix + "." + fieldReference;
  }
}
