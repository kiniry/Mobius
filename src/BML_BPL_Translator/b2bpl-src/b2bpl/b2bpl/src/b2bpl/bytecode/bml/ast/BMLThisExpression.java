package b2bpl.bytecode.bml.ast;

import b2bpl.bytecode.bml.BMLExpressionVisitor;


public class BMLThisExpression extends BMLExpression {

  public static final BMLThisExpression THIS = new BMLThisExpression();

  private BMLThisExpression() {
    // hide the constructor
  }

  public <R> R accept(BMLExpressionVisitor<R> visitor) {
    return visitor.visitThisExpression(this);
  }

  public String toString() {
    return "this";
  }
}
