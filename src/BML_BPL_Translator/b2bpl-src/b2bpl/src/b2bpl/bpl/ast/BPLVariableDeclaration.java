package b2bpl.bpl.ast;

import b2bpl.bpl.IBPLVisitor;


public class BPLVariableDeclaration extends BPLDeclaration {

  public static final BPLVariableDeclaration[] EMPTY_ARRAY =
    new BPLVariableDeclaration[0];

  private final BPLVariable[] variables;

  public BPLVariableDeclaration(BPLVariable... variables) {
    this.variables = variables;
  }

  public BPLVariable[] getVariables() {
    return variables;
  }

  public <R> R accept(IBPLVisitor<R> visitor) {
    return visitor.visitVariableDeclaration(this);
  }

  public String toString() {
    StringBuffer sb = new StringBuffer();

    sb.append("var ");
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
