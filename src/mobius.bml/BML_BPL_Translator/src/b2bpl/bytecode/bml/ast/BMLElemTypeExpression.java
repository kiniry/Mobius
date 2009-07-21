package b2bpl.bytecode.bml.ast;

import b2bpl.bytecode.bml.IBMLExpressionVisitor;


public class BMLElemTypeExpression extends BMLExpression {

  private final BMLExpression typeExpression;

  public BMLElemTypeExpression(BMLExpression expression) {
    this.typeExpression = expression;
  }

  public BMLExpression getTypeExpression() {
    return typeExpression;
  }

  public <R> R accept(IBMLExpressionVisitor<R> visitor) {
    return visitor.visitElemTypeExpression(this);
  }

  public String toString() {
    return "\\elemtype(" + typeExpression + ")";
  }
}
