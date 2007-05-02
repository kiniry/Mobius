package b2bpl.bpl.ast;

import b2bpl.bpl.IBPLVisitor;


public class BPLVariableExpression extends BPLExpression {

  public static final BPLVariableExpression[] EMPTY_ARRAY = new BPLVariableExpression[0];

  private final String identifier;

  private BPLVariable variable;

  public BPLVariableExpression(String identifier) {
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

  public <R> R accept(IBPLVisitor<R> visitor) {
    return visitor.visitVariableExpression(this);
  }

  public String toString() {
    return identifier;
  }
}
