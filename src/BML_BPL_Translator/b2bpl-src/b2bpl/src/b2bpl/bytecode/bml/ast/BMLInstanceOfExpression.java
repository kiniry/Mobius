package b2bpl.bytecode.bml.ast;

import b2bpl.bytecode.JType;
import b2bpl.bytecode.bml.IBMLExpressionVisitor;


public class BMLInstanceOfExpression extends BMLExpression {

  private final BMLExpression expression;

  private final JType targetType;

  public BMLInstanceOfExpression(BMLExpression expression, JType targetType) {
    this.expression = expression;
    this.targetType = targetType;
  }

  public BMLExpression getExpression() {
    return expression;
  }

  public JType getTargetType() {
    return targetType;
  }

  public boolean isPredicate() {
    return true;
  }

  public <R> R accept(IBMLExpressionVisitor<R> visitor) {
    return visitor.visitInstanceOfExpression(this);
  }

  public String toString() {
    return expression + " instanceof " + targetType;
  }
}
