package b2bpl.bpl.ast;

import b2bpl.bpl.BPLVisitor;


public class BPLQuantifierExpression extends BPLExpression {

  private final Operator operator;

  private final BPLVariable[] variables;

  private final BPLTrigger[] triggers;

  private final BPLExpression expression;

  public BPLQuantifierExpression(
      Operator operator,
      BPLVariable[] variables,
      BPLExpression expression) {
    this(operator, variables, BPLTrigger.EMPTY_ARRAY, expression);
  }

  public BPLQuantifierExpression(
      Operator operator,
      BPLVariable[] variables,
      BPLTrigger[] triggers,
      BPLExpression expression) {
    super(Precedence.ATOM);
    this.operator = operator;
    this.variables = variables;
    this.triggers = triggers;
    this.expression = expression;
  }

  public boolean isPredicate() {
    return true;
  }

  public <R> R accept(BPLVisitor<R> visitor) {
    return visitor.visitQuantifierExpression(this);
  }

  public Operator getOperator() {
    return operator;
  }

  public BPLVariable[] getVariables() {
    return variables;
  }

  public BPLTrigger[] getTriggers() {
    return triggers;
  }

  public BPLExpression getExpression() {
    return expression;
  }

  public String toString() {
    StringBuffer sb = new StringBuffer();

    sb.append('(');
    sb.append(operator);
    sb.append(' ');
    for (int i = 0; i < variables.length; i++) {
      if (i > 0) {
        sb.append(", ");
      }
      sb.append(variables[i]);
    }
    sb.append(" :: ");
    for (int i = 0; i < triggers.length; i++) {
      sb.append("{ ").append(triggers[i]).append(" }");  
      sb.append(' ');
    }
    sb.append(expression);
    sb.append(')');

    return sb.toString();
  }

  public static enum Operator {

    FORALL("forall"),

    EXISTS("exists");

    private final String token;

    private Operator(String token) {
      this.token = token;
    }

    public String toString() {
      return token;
    }
  }
}
