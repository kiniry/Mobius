package b2bpl.bpl.ast;

import b2bpl.bpl.IBPLVisitor;


public class BPLPartialOrderExpression extends BPLBinaryExpression {

  public BPLPartialOrderExpression(BPLExpression left, BPLExpression right) {
    super(Precedence.RELATIONAL, left, right);
  }

  public boolean isPredicate() {
    return true;
  }

  public boolean isLeftAssociativeTo(BPLExpression other) {
    return false;
  }

  public boolean isRightAssociativeTo(BPLExpression other) {
    return false;
  }

  public <R> R accept(IBPLVisitor<R> visitor) {
    return visitor.visitPartialOrderExpression(this);
  }

  public String toString() {
    return opndToString(left) + " <: " + opndToString(right);
  }
}
