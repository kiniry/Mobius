package b2bpl.bytecode.bml.ast;

import b2bpl.bytecode.bml.BMLExpressionVisitor;


public class BMLLogicalNotExpression extends BMLUnaryExpression {

  public BMLLogicalNotExpression(BMLExpression expression) {
    super(expression);
  }

  public boolean isPredicate() {
    return true;
  }

  public <R> R accept(BMLExpressionVisitor<R> visitor) {
    return visitor.visitLogicalNotExpression(this);
  }

  public String toString() {
    return "!" + expression;
  }
}
