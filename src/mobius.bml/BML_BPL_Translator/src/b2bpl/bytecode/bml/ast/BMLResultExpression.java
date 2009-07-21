package b2bpl.bytecode.bml.ast;

import b2bpl.bytecode.bml.IBMLExpressionVisitor;


public class BMLResultExpression extends BMLExpression {

  public static final BMLResultExpression RESULT = new BMLResultExpression();

  private BMLResultExpression() {
    // hide the constructor
  }

  public <R> R accept(IBMLExpressionVisitor<R> visitor) {
    return visitor.visitResultExpression(this);
  }

  public String toString() {
    return "\\result";
  }
}
