package b2bpl.bytecode.bml.ast;

import b2bpl.bytecode.bml.BMLExpressionVisitor;


public class BMLSuperExpression extends BMLExpression {

  public static final BMLSuperExpression SUPER = new BMLSuperExpression();

  private BMLSuperExpression() {
    // hide the constructor
  }

  public <R> R accept(BMLExpressionVisitor<R> visitor) {
    // TODO[om]: Implement
    return null;
  }

  public String toString() {
    return "super";
  }
}
