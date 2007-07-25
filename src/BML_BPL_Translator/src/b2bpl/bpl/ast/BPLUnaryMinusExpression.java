package b2bpl.bpl.ast;

import b2bpl.bpl.IBPLVisitor;


public class BPLUnaryMinusExpression extends BPLUnaryExpression {

  public BPLUnaryMinusExpression(BPLExpression expression) {
    super(expression);
  }

  public <R> R accept(IBPLVisitor<R> visitor) {
    return visitor.visitUnaryMinusExpression(this);
  }

  public String toString() {
    return "-" + opndToString(expression);
  }
}
