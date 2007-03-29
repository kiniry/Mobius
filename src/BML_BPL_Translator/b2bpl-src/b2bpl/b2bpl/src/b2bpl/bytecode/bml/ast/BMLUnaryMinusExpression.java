package b2bpl.bytecode.bml.ast;

import b2bpl.bytecode.bml.BMLExpressionVisitor;


public class BMLUnaryMinusExpression extends BMLUnaryExpression {

  public BMLUnaryMinusExpression(BMLExpression expression) {
    super(expression);
  }

  public <R> R accept(BMLExpressionVisitor<R> visitor) {
    return visitor.visitUnaryMinusExpression(this);
  }

  public String toString() {
    return "-" + expression;
  }
}
