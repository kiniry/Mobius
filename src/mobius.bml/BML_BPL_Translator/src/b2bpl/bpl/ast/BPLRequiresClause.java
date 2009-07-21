package b2bpl.bpl.ast;

import b2bpl.bpl.IBPLVisitor;


public class BPLRequiresClause extends BPLSpecificationClause {

  private final boolean isFree;

  private final BPLExpression expression;

  public BPLRequiresClause(BPLExpression expression) {
    this(false, expression);
  }

  public BPLRequiresClause(boolean isFree, BPLExpression expression) {
    this.isFree = isFree;
    this.expression = expression;
  }

  public boolean isFree() {
    return isFree;
  }

  public BPLExpression getExpression() {
    return expression;
  }

  public <R> R accept(IBPLVisitor<R> visitor) {
    return visitor.visitRequiresClause(this);
  }

  public String toString() {
    return "requires " + expression + ";";
  }
}
