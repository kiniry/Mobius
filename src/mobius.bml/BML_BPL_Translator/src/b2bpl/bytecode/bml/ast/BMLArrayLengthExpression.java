package b2bpl.bytecode.bml.ast;

import b2bpl.bytecode.bml.IBMLExpressionVisitor;


public class BMLArrayLengthExpression extends BMLExpression {

  private final BMLExpression prefix;

  public BMLArrayLengthExpression(BMLExpression prefix) {
    this.prefix = prefix;
  }

  public BMLExpression getPrefix() {
    return prefix;
  }

  public <R> R accept(IBMLExpressionVisitor<R> visitor) {
    return visitor.visitArrayLengthExpression(this);
  }

  public String toString() {
    return prefix + ".length";
  }
}
