package b2bpl.bpl.ast;

import b2bpl.bpl.BPLVisitor;


public class BPLCallCommand extends BPLCommand {

  private final String procedureName;

  private final BPLExpression[] arguments;

  private final BPLVariableExpression[] resultVariables;

  private BPLProcedure procedure;

  public BPLCallCommand(String procedureName, BPLExpression... arguments) {
    this(procedureName, arguments, BPLVariableExpression.EMPTY_ARRAY);
  }

  public BPLCallCommand(
      String procedureName,
      BPLExpression[] arguments,
      BPLVariableExpression... resultVariables) {
    this.procedureName = procedureName;
    this.arguments = arguments;
    this.resultVariables = resultVariables;
  }

  public String getProcedureName() {
    return procedureName;
  }

  public BPLExpression[] getArguments() {
    return arguments;
  }

  public BPLVariableExpression[] getResultVariables() {
    return resultVariables;
  }

  public BPLProcedure getProcedure() {
    return procedure;
  }

  public void setProcedure(BPLProcedure procedure) {
    this.procedure = procedure;
  }

  public boolean isPassive() {
    return false;
  }

  public <R> R accept(BPLVisitor<R> visitor) {
    return visitor.visitCallCommand(this);
  }

  public String toString() {
    StringBuffer sb = new StringBuffer();

    sb.append("call ");
    if (resultVariables.length > 0) {
      for (int i = 0; i < resultVariables.length; i++) {
        if (i > 0) {
          sb.append(", ");
        }
        sb.append(resultVariables[i]);
      }
      sb.append(" := ");
    }
    sb.append(procedureName);
    sb.append('(');
    for (int i = 0; i < arguments.length; i++) {
      if (i > 0) {
        sb.append(", ");
      }
      sb.append(arguments[i]);
    }
    sb.append(')');
    sb.append(';');

    return sb.toString();
  }
}
