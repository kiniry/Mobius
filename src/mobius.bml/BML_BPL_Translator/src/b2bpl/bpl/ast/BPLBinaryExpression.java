package b2bpl.bpl.ast;


public abstract class BPLBinaryExpression extends BPLExpression {

  protected final BPLExpression left;

  protected final BPLExpression right;

  public BPLBinaryExpression(
      Precedence precedence,
      BPLExpression left,
      BPLExpression right) {
    super(precedence);
    this.left = left;
    this.right = right;
  }

  public BPLExpression getLeft() {
    return left;
  }

  public BPLExpression getRight() {
    return right;
  }

  public abstract boolean isLeftAssociativeTo(BPLExpression other);

  public abstract boolean isRightAssociativeTo(BPLExpression other);

  protected String opndToString(BPLExpression opnd) {
    if (opnd != null) {
      if (precedence.compare(opnd.precedence) > 0) {
        return "(" + opnd + ")";
      } else if (precedence.compare(opnd.precedence) == 0) {
        if ((opnd == left) && !isLeftAssociativeTo(opnd)) {
          return "(" + opnd + ")";
        } else if ((opnd == right) && !isRightAssociativeTo(opnd)) {
          return "(" + opnd + ")";
        }
      }
      return opnd.toString();
    }
    return "null";
  }
}
