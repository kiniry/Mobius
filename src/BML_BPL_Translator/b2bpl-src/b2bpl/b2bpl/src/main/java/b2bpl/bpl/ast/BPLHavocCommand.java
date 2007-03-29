package b2bpl.bpl.ast;

import b2bpl.bpl.BPLVisitor;


public class BPLHavocCommand extends BPLCommand {

  private final BPLVariableExpression[] variables;

  public BPLHavocCommand(BPLVariableExpression... variables) {
    this.variables = variables;
  }

  public BPLVariableExpression[] getVariables() {
    return variables;
  }

  public boolean isPassive() {
    return false;
  }

  public <R> R accept(BPLVisitor<R> visitor) {
    return visitor.visitHavocCommand(this);
  }

  public String toString() {
    StringBuffer sb = new StringBuffer();

    sb.append("havoc ");
    for (int i = 0; i < variables.length; i++) {
      if (i > 0) {
        sb.append(", ");
      }
      sb.append(variables[i]);
    }
    sb.append(';');

    return sb.toString();
  }
}
