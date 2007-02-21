package b2bpl.bytecode.bml.ast;

import b2bpl.bytecode.JType;
import b2bpl.bytecode.bml.BMLExpressionVisitor;


public class BMLQuantifierExpression extends BMLExpression {

  private final Operator operator;

  private final JType[] variableTypes;

  private final BMLExpression expression;

  public BMLQuantifierExpression(
      Operator operator,
      JType[] variableTypes,
      BMLExpression expression) {
    this.operator = operator;
    this.variableTypes = variableTypes;
    this.expression = expression;
  }

  public Operator getOperator() {
    return operator;
  }

  public BMLExpression getExpression() {
    return expression;
  }

  public JType[] getVariableTypes() {
    return variableTypes;
  }

  public boolean isPredicate() {
    return true;
  }

  public <R> R accept(BMLExpressionVisitor<R> visitor) {
    return visitor.visitQuantifierExpression(this);
  }

  public String toString() {
    StringBuffer sb = new StringBuffer();

    sb.append('(').append(operator).append(' ');
    for (int i = 0; i < variableTypes.length; i++) {
      if (i > 0) {
        sb.append(", ");
      }
      sb.append(variableTypes[i]);
    }
    sb.append("; ").append(expression).append(')');

    return sb.toString();
  }

  public static enum Operator {

    FORALL("\\forall"),

    EXISTS("\\exists");

    private final String token;

    private Operator(String token) {
      this.token = token;
    }

    public String toString() {
      return token;
    }
  }
}
