package b2bpl.bytecode.bml.ast;

import b2bpl.bytecode.bml.IBMLExpressionVisitor;


public class BMLUnaryMinusExpression extends BMLUnaryExpression {

  public BMLUnaryMinusExpression(BMLExpression expression) {
    super(expression);
  }

  public <R> R accept(IBMLExpressionVisitor<R> visitor) {
    return visitor.visitUnaryMinusExpression(this);
  }

  public String toString() {
    return "-" + expression;
  }
}
