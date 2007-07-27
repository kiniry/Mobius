package b2bpl.bytecode.bml.ast;

import b2bpl.bytecode.bml.IBMLExpressionVisitor;


public class BMLArrayAccessExpression extends BMLExpression {

  private final BMLExpression prefix;

  private final BMLExpression index;

  public BMLArrayAccessExpression(BMLExpression prefix, BMLExpression index) {
    this.prefix = prefix;
    this.index = index;
  }

  public BMLExpression getPrefix() {
    return prefix;
  }

  public BMLExpression getIndex() {
    return index;
  }

  public <R> R accept(IBMLExpressionVisitor<R> visitor) {
    return visitor.visitArrayAccessExpression(this);
  }

  public String toString() {
    return prefix + "[" + index + "]";
  }
}
