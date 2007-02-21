package b2bpl.bytecode.bml.ast;

import b2bpl.bytecode.bml.BMLExpressionVisitor;


public class BMLArrayLengthExpression extends BMLExpression {

  private final BMLExpression prefix;

  public BMLArrayLengthExpression(BMLExpression prefix) {
    this.prefix = prefix;
  }

  public BMLExpression getPrefix() {
    return prefix;
  }

  public <R> R accept(BMLExpressionVisitor<R> visitor) {
    return visitor.visitArrayLengthExpression(this);
  }

  public String toString() {
    return prefix + ".length";
  }
}
