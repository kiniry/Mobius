package b2bpl.bpl.ast;

import b2bpl.bpl.BPLVisitor;


public class BPLOldExpression extends BPLExpression {

  private final BPLExpression expression;

  public BPLOldExpression(BPLExpression expression) {
    super(Precedence.ATOM);
    this.expression = expression;
  }

  public BPLExpression getExpression() {
    return expression;
  }

  public boolean isPredicate() {
    return expression.isPredicate();
  }

  public <R> R accept(BPLVisitor<R> visitor) {
    return visitor.visitOldExpression(this);
  }
}
