package b2bpl.bpl.ast;

import b2bpl.bpl.IBPLVisitor;


public class BPLCastExpression extends BPLExpression {

  private final BPLExpression expression;

  private final BPLType targetType;

  public BPLCastExpression(BPLExpression expression, BPLType targetType) {
    super(Precedence.ATOM);
    this.expression = expression;
    this.targetType = targetType;
  }

  public BPLExpression getExpression() {
    return expression;
  }

  public BPLType getTargetType() {
    return targetType;
  }

  public <R> R accept(IBPLVisitor<R> visitor) {
    return visitor.visitCastExpression(this);
  }
}
