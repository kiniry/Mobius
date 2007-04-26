package b2bpl.bpl.ast;

import b2bpl.bpl.BPLVisitor;


public class BPLOldVariableExpression extends BPLExpression {

  public static final BPLOldVariableExpression[] EMPTY_ARRAY = new BPLOldVariableExpression[0];

  private final String identifier;

  private BPLVariable variable;

  public BPLOldVariableExpression(String identifier) {
    super(Precedence.ATOM);
    this.identifier = identifier;
  }

  public String getIdentifier() {
    return identifier;
  }

  public BPLVariable getVariable() {
    return variable;
  }

  public void setVariable(BPLVariable variable) {
    this.variable = variable;
  }

  public <R> R accept(BPLVisitor<R> visitor) {
    return visitor.visitOldVariableExpression(this);
  }

  public String toString() {
    return identifier;
  }
}
