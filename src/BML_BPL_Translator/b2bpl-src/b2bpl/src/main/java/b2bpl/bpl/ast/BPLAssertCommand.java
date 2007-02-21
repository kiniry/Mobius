package b2bpl.bpl.ast;

import b2bpl.bpl.BPLVisitor;


public class BPLAssertCommand extends BPLCommand {

  private final BPLExpression expression;

  public BPLAssertCommand(BPLExpression expression) {
    this.expression = expression;
  }

  public BPLExpression getExpression() {
    return expression;
  }

  public boolean isPassive() {
    return true;
  }

  public <R> R accept(BPLVisitor<R> visitor) {
    return visitor.visitAssertCommand(this);
  }

  public String toString() {
    return "assert " + expression + ";";
  }
}
