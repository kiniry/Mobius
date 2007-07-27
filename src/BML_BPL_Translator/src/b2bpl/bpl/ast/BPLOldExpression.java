package b2bpl.bpl.ast;

import b2bpl.bpl.IBPLVisitor;


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

  public <R> R accept(IBPLVisitor<R> visitor) {
    return visitor.visitOldExpression(this);
  }
  
  public String toString() {
    return "old(" + expression.toString() + ")";
  }
}
