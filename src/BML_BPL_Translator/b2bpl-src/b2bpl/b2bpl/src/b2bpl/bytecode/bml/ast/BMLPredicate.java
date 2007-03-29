package b2bpl.bytecode.bml.ast;

import b2bpl.bytecode.bml.BMLExpressionVisitor;


public class BMLPredicate extends BMLExpression {

  private final BMLExpression expression;

  public BMLPredicate(BMLExpression expression) {
    this.expression = expression;
  }

  public BMLExpression getExpression() {
    return expression;
  }

  public boolean isPredicate() {
    return expression.isPredicate();
  }

  public <R> R accept(BMLExpressionVisitor<R> visitor) {
    return visitor.visitPredicate(this);
  }

  public String toString() {
    return expression.toString();
  }
}
