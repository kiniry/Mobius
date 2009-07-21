package b2bpl.bytecode.bml.ast;

import b2bpl.bytecode.bml.IBMLExpressionVisitor;


public class BMLTypeOfExpression extends BMLExpression {

  private final BMLExpression expression;

  public BMLTypeOfExpression(BMLExpression expression) {
    this.expression = expression;
  }

  public BMLExpression getExpression() {
    return expression;
  }

  public <R> R accept(IBMLExpressionVisitor<R> visitor) {
    return visitor.visitTypeOfExpression(this);
  }

  public String toString() {
    return "\\typeof(" + expression + ")";
  }
}
