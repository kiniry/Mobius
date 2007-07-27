package b2bpl.bytecode.bml.ast;

import b2bpl.bytecode.bml.IBMLExpressionVisitor;


public class BMLBoundVariableExpression extends BMLExpression {

  private final int index;

  public BMLBoundVariableExpression(int index) {
    this.index = index;
  }

  public int getIndex() {
    return index;
  }

  public <R> R accept(IBMLExpressionVisitor<R> visitor) {
    return visitor.visitBoundVariableExpression(this);
  }

  public String toString() {
    return "\\bv(" + index + ")";
  }
}
