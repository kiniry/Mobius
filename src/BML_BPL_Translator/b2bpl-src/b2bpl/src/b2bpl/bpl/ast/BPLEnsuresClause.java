package b2bpl.bpl.ast;

import b2bpl.bpl.IBPLVisitor;


public class BPLEnsuresClause extends BPLSpecificationClause {

  private final boolean isFree;

  private final BPLExpression expression;

  public BPLEnsuresClause(BPLExpression expression) {
    this(false, expression);
  }

  public BPLEnsuresClause(boolean isFree, BPLExpression expression) {
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
    return visitor.visitEnsuresClause(this);
  }

  public String toString() {
    return "ensures " + expression + ";";
  }
}
