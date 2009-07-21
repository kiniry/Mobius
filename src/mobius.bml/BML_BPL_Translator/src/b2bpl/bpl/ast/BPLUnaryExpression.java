package b2bpl.bpl.ast;


public abstract class BPLUnaryExpression extends BPLExpression {

  protected final BPLExpression expression;

  public BPLUnaryExpression(BPLExpression expression) {
    super(Precedence.UNARY);
    this.expression = expression;
  }

  public BPLExpression getExpression() {
    return expression;
  }

  protected String opndToString(BPLExpression opnd) {
    if (opnd != null) {
      if (precedence.compare(opnd.precedence) > 0) {
        return "(" + opnd + ")";
      }
      return opnd.toString();
    }
    return "null";
  }
}
