package b2bpl.bpl.ast;

import b2bpl.bpl.BPLVisitor;


public class BPLRelationalExpression extends BPLBinaryExpression {

  private final Operator operator;

  public BPLRelationalExpression(
      Operator operator,
      BPLExpression left,
      BPLExpression right) {
    super(Precedence.RELATIONAL, left, right);
    this.operator = operator;
  }

  public Operator getOperator() {
    return operator;
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

  public <R> R accept(BPLVisitor<R> visitor) {
    return visitor.visitRelationalExpression(this);
  }

  public String toString() {
    return opndToString(left) + " " + operator + " " + opndToString(right);
  }

  public static enum Operator {

    LESS("<"),

    GREATER(">"),

    LESS_EQUAL("<="),

    GREATER_EQUAL(">=");

    private final String token;

    private Operator(String token) {
      this.token = token;
    }

    public String toString() {
      return token;
    }
  }
}
