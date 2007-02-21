package b2bpl.bpl.ast;

import b2bpl.bpl.BPLVisitor;


public class BPLUnaryMinusExpression extends BPLUnaryExpression {

  public BPLUnaryMinusExpression(BPLExpression expression) {
    super(expression);
  }

  public <R> R accept(BPLVisitor<R> visitor) {
    return visitor.visitUnaryMinusExpression(this);
  }

  public String toString() {
    return "-" + opndToString(expression);
  }
}
