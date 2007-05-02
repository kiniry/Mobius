package b2bpl.bytecode.bml.ast;

import b2bpl.bytecode.bml.IBMLExpressionVisitor;


public class BMLIntLiteral extends BMLLiteral {

  private final int value;

  public BMLIntLiteral(int value) {
    this.value = value;
  }

  public int getValue() {
    return value;
  }

  public <R> R accept(IBMLExpressionVisitor<R> visitor) {
    return visitor.visitIntLiteral(this);
  }

  public String toString() {
    return String.valueOf(value);
  }
}
