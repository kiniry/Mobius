package b2bpl.bytecode.bml.ast;


public abstract class BMLUnaryExpression extends BMLExpression {

  protected final BMLExpression expression;

  public BMLUnaryExpression(BMLExpression expression) {
    this.expression = expression;
  }

  public BMLExpression getExpression() {
    return expression;
  }
}
