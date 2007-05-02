package b2bpl.bytecode.bml.ast;

import b2bpl.bytecode.bml.IBMLExpressionVisitor;


public class BMLNullLiteral extends BMLLiteral {

  public static final BMLNullLiteral NULL = new BMLNullLiteral();

  private BMLNullLiteral() {
    // hide the constructor
  }

  public <R> R accept(IBMLExpressionVisitor<R> visitor) {
    return visitor.visitNullLiteral(this);
  }

  public String toString() {
    return "null";
  }
}
