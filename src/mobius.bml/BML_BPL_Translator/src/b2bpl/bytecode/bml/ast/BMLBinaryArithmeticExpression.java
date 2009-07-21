package b2bpl.bytecode.bml.ast;

import b2bpl.bytecode.bml.IBMLExpressionVisitor;


public class BMLBinaryArithmeticExpression extends BMLBinaryExpression {

  private final Operator operator;

  public BMLBinaryArithmeticExpression(
      Operator operator,
      BMLExpression left,
      BMLExpression right) {
    super(left, right);
    this.operator = operator;
  }

  public Operator getOperator() {
    return operator;
  }

  public <R> R accept(IBMLExpressionVisitor<R> visitor) {
    return visitor.visitBinaryArithmeticExpression(this);
  }

  public String toString() {
    return left + " " + operator + " " + right;
  }

  public static enum Operator {

    PLUS("+"),

    MINUS("-"),

    TIMES("*"),

    DIVIDE("/"),

    REMAINDER("%");

    private final String token;

    private Operator(String token) {
      this.token = token;
    }

    public String toString() {
      return token;
    }
  }
}
