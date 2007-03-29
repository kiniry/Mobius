package b2bpl.bpl.ast;

import b2bpl.bpl.BPLVisitor;


public class BPLAssumeCommand extends BPLCommand {

  private final BPLExpression expression;

  public BPLAssumeCommand(BPLExpression expression) {
    this.expression = expression;
  }

  public BPLExpression getExpression() {
    return expression;
  }

  public boolean isPassive() {
    return true;
  }

  public <R> R accept(BPLVisitor<R> visitor) {
    return visitor.visitAssumeCommand(this);
  }

  public String toString() {
    return "assume " + expression + ";";
  }
}
