package b2bpl.bpl.ast;

import b2bpl.bpl.BPLVisitor;


public class BPLEqualityExpression extends BPLBinaryExpression {

  private final Operator operator;

  public BPLEqualityExpression(
      Operator operator,
      BPLExpression left,
      BPLExpression right) {
    super(Precedence.EQUALITY, left, right);
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
    return visitor.visitEqualityExpression(this);
  }

  public String toString() {
    return opndToString(left) + " " + operator + " " + opndToString(right);
  }

  public static enum Operator {

    EQUALS("=="),

    NOT_EQUALS("!=");

    private final String token;

    private Operator(String token) {
      this.token = token;
    }

    public String toString() {
      return token;
    }
  }
}
