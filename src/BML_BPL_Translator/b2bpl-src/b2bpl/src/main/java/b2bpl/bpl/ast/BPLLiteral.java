package b2bpl.bpl.ast;


public abstract class BPLLiteral extends BPLExpression {

  protected BPLLiteral() {
    super(Precedence.ATOM);
  }
}
