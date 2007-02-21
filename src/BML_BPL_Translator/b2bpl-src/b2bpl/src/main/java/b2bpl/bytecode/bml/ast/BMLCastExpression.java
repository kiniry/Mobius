package b2bpl.bytecode.bml.ast;

import b2bpl.bytecode.JType;
import b2bpl.bytecode.bml.BMLExpressionVisitor;


public class BMLCastExpression extends BMLExpression {

  private final JType targetType;

  private final BMLExpression expression;

  public BMLCastExpression(JType targetType, BMLExpression expression) {
    this.targetType = targetType;
    this.expression = expression;
  }

  public JType getTargetType() {
    return targetType;
  }

  public BMLExpression getExpression() {
    return expression;
  }

  public <R> R accept(BMLExpressionVisitor<R> visitor) {
    return visitor.visitCastExpression(this);
  }

  public String toString() {
    return "(" + targetType + ") " + expression;
  }
}
