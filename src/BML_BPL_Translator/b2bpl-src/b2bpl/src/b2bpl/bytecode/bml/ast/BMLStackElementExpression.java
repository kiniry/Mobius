package b2bpl.bytecode.bml.ast;

import b2bpl.bytecode.bml.IBMLExpressionVisitor;


public class BMLStackElementExpression extends BMLExpression {

  private final BMLExpression indexExpression;

  private int index = -1;

  public BMLStackElementExpression(BMLExpression indexExpression) {
    this.indexExpression = indexExpression;
  }

  public BMLExpression getIndexExpression() {
    return indexExpression;
  }

  public int getIndex() {
    return index;
  }

  public void setIndex(int index) {
    this.index = index;
  }

  public <R> R accept(IBMLExpressionVisitor<R> visitor) {
    return visitor.visitStackElementExpression(this);
  }

  public String toString() {
    return "\\st(" + indexExpression + ")";
  }
}
