package b2bpl.bytecode.bml.ast;


public class BMLLoopVariant extends BMLNode {

  private final BMLExpression expression;

  public BMLLoopVariant(BMLExpression expression) {
    this.expression = expression;
  }

  public BMLExpression getExpression() {
    return expression;
  }

  public String toString() {
    return "loop_variant " + expression + ";";
  }
}
