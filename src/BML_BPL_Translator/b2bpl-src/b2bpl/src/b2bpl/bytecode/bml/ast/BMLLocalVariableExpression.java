package b2bpl.bytecode.bml.ast;

import b2bpl.bytecode.bml.IBMLExpressionVisitor;


public class BMLLocalVariableExpression extends BMLExpression {

  private final int index;

  public BMLLocalVariableExpression(int index) {
    this.index = index;
  }

  public int getIndex() {
    return index;
  }

  public <R> R accept(IBMLExpressionVisitor<R> visitor) {
    return visitor.visitLocalVariableExpression(this);
  }

  public String toString() {
    return "\\lv(" + index + ")";
  }
}
