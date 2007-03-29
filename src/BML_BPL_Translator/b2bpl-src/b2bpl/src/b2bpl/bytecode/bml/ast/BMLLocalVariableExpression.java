package b2bpl.bytecode.bml.ast;

import b2bpl.bytecode.bml.BMLExpressionVisitor;


public class BMLLocalVariableExpression extends BMLExpression {

  private final int index;

  public BMLLocalVariableExpression(int index) {
    this.index = index;
  }

  public int getIndex() {
    return index;
  }

  public <R> R accept(BMLExpressionVisitor<R> visitor) {
    return visitor.visitLocalVariableExpression(this);
  }

  public String toString() {
    return "\\lv(" + index + ")";
  }
}
