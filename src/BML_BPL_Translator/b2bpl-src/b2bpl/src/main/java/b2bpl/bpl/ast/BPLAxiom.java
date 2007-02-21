package b2bpl.bpl.ast;

import b2bpl.bpl.BPLVisitor;


public class BPLAxiom extends BPLDeclaration {

  private final BPLExpression expression;

  public BPLAxiom(BPLExpression expression) {
    this.expression = expression;
  }

  public BPLExpression getExpression() {
    return expression;
  }

  public <R> R accept(BPLVisitor<R> visitor) {
    return visitor.visitAxiom(this);
  }

  public String toString() {
    return "axiom " + expression + ";";
  }
}
