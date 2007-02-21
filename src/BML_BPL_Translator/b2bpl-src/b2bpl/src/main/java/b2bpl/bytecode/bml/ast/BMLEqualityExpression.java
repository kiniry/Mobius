package b2bpl.bytecode.bml.ast;

import b2bpl.bytecode.bml.BMLExpressionVisitor;


public class BMLEqualityExpression extends BMLBinaryExpression {

  private final Operator operator;

  public BMLEqualityExpression(
      Operator operator,
      BMLExpression left,
      BMLExpression right) {
    super(left, right);
    this.operator = operator;
  }

  public Operator getOperator() {
    return operator;
  }

  public boolean isPredicate() {
    return true;
  }

  public <R> R accept(BMLExpressionVisitor<R> visitor) {
    return visitor.visitEqualityExpression(this);
  }

  public String toString() {
    return left + " " + operator + " " + right;
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
