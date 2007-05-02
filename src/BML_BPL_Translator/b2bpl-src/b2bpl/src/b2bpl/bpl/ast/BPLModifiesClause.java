package b2bpl.bpl.ast;

import b2bpl.bpl.IBPLVisitor;


public class BPLModifiesClause extends BPLSpecificationClause {

  private final BPLVariableExpression[] variables;

  public BPLModifiesClause(BPLVariableExpression... variables) {
    this.variables = variables;
  }

  public BPLVariableExpression[] getVariables() {
    return variables;
  }

  public <R> R accept(IBPLVisitor<R> visitor) {
    return visitor.visitModifiesClause(this);
  }

  public String toString() {
    StringBuffer sb = new StringBuffer();

    sb.append("modifies ");
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
