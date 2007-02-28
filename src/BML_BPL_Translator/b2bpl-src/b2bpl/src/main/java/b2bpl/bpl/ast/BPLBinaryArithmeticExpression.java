package b2bpl.bpl.ast;

import b2bpl.bpl.BPLVisitor;


public class BPLBinaryArithmeticExpression extends BPLBinaryExpression {

  private final Operator operator;

  public BPLBinaryArithmeticExpression(
      Operator operator,
      BPLExpression left,
      BPLExpression right) {
    super(operator.precedence, left, right);
    this.operator = operator;
  }

  public Operator getOperator() {
    return operator;
  }

  public boolean isLeftAssociativeTo(BPLExpression other) {
    return ((other instanceof BPLBinaryArithmeticExpression)
        && (precedence.compare(other.precedence) == 0));
  }

  public boolean isRightAssociativeTo(BPLExpression other) {
    if (operator.equals(Operator.PLUS) || operator.equals(Operator.TIMES)) {
      return ((other instanceof BPLBinaryArithmeticExpression)
          && (operator.equals(((BPLBinaryArithmeticExpression) other).operator)));
    }
    return false;
  }

  public <R> R accept(BPLVisitor<R> visitor) {
    return visitor.visitBinaryArithmeticExpression(this);
  }

  public String toString() {
    return opndToString(left) + " " + operator + " " + opndToString(right);
  }

  public static enum Operator {

    PLUS("+", Precedence.ADDITIVE),

    MINUS("-", Precedence.ADDITIVE),

    TIMES("*", Precedence.MULTIPLICATIVE),

    DIVIDE("/", Precedence.MULTIPLICATIVE),

    REMAINDER("%", Precedence.MULTIPLICATIVE);

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
