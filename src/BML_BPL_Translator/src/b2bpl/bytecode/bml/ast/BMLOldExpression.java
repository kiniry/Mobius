package b2bpl.bytecode.bml.ast;

import b2bpl.bytecode.bml.IBMLExpressionVisitor;


public class BMLOldExpression extends BMLExpression {

  private final BMLExpression expression;

  public BMLOldExpression(BMLExpression expression) {
    this.expression = expression;
  }

  public BMLExpression getExpression() {
    return expression;
  }

  public boolean isPredicate() {
    return expression.isPredicate();
  }

  public <R> R accept(IBMLExpressionVisitor<R> visitor) {
    return visitor.visitOldExpression(this);
  }

  public String toString() {
    return "\\old(" + expression + ")";
  }
}
