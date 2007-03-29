package b2bpl.bpl.ast;

import b2bpl.bpl.BPLVisitor;


public class BPLBinaryLogicalExpression extends BPLBinaryExpression {

  private final Operator operator;

  public BPLBinaryLogicalExpression(
      Operator operator,
      BPLExpression left,
      BPLExpression right) {
    super(operator.precedence, left, right);
    this.operator = operator;
  }

  public Operator getOperator() {
    return operator;
  }

  public boolean isPredicate() {
    return true;
  }

  public boolean isAssociativeTo(BPLExpression other) {
    return ((other instanceof BPLBinaryLogicalExpression)
        && (operator.equals(((BPLBinaryLogicalExpression) other).operator)));
  }

  public boolean isLeftAssociativeTo(BPLExpression other) {
    if (operator.equals(Operator.IMPLIES)) {
      return false;
    }
    return isAssociativeTo(other);
  }

  public boolean isRightAssociativeTo(BPLExpression other) {
    return isAssociativeTo(other);
  }

  public <R> R accept(BPLVisitor<R> visitor) {
    return visitor.visitBinaryLogicalExpression(this);
  }

  public String toString() {
    return opndToString(left) + " " + operator + " " + opndToString(right);
  }

  public static enum Operator {

    AND("&&", Precedence.AND_OR),

    OR("||", Precedence.AND_OR),

    IMPLIES("==>", Precedence.IMPLICATION),

    EQUIVALENCE("<==>", Precedence.EQUIVALENCE);

    private final String token;

    private final Precedence precedence;

    private Operator(String token, Precedence precedence) {
      this.token = token;
      this.precedence = precedence;
    }

    public String toString() {
      return token;
    }
  }
}
