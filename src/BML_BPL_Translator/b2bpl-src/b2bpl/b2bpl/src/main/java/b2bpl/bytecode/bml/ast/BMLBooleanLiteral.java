package b2bpl.bytecode.bml.ast;

import b2bpl.bytecode.bml.BMLExpressionVisitor;


public class BMLBooleanLiteral extends BMLLiteral {

  public static final BMLBooleanLiteral TRUE = new BMLBooleanLiteral(true);

  public static final BMLBooleanLiteral FALSE = new BMLBooleanLiteral(false);

  private final boolean value;

  private BMLBooleanLiteral(boolean value) {
    this.value = value;
  }

  public boolean getValue() {
    return value;
  }

  public boolean isPredicate() {
    return true;
  }

  public <R> R accept(BMLExpressionVisitor<R> visitor) {
    return visitor.visitBooleanLiteral(this);
  }

  public String toString() {
    return String.valueOf(value);
  }
}
