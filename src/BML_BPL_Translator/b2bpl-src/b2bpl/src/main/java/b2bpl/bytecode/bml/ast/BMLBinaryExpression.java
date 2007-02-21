package b2bpl.bytecode.bml.ast;


public abstract class BMLBinaryExpression extends BMLExpression {

  protected final BMLExpression left;

  protected final BMLExpression right;

  public BMLBinaryExpression(BMLExpression left, BMLExpression right) {
    this.left = left;
    this.right = right;
  }

  public BMLExpression getLeft() {
    return left;
  }

  public BMLExpression getRight() {
    return right;
  }
}
