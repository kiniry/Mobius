package b2bpl.bpl.ast;

import b2bpl.bpl.BPLVisitor;


public class BPLLogicalNotExpression extends BPLUnaryExpression {

  public BPLLogicalNotExpression(BPLExpression expression) {
    super(expression);
  }

  public boolean isPredicate() {
    return true;
  }

  public <R> R accept(BPLVisitor<R> visitor) {
    return visitor.visitLogicalNotExpression(this);
  }

  public String toString() {
    return "!" + opndToString(expression);
  }
}
