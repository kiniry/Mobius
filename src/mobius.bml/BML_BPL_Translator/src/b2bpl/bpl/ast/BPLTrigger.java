package b2bpl.bpl.ast;

import b2bpl.bpl.IBPLVisitor;


public class BPLTrigger extends BPLNode {

  public static final BPLTrigger[] EMPTY_ARRAY = new BPLTrigger[0];

  private final BPLExpression[] expressions;

  public BPLTrigger(BPLExpression... expressions) {
    this.expressions = expressions;
  }

  public BPLExpression[] getExpressions() {
    return expressions;
  }

  public <R> R accept(IBPLVisitor<R> visitor) {
    return visitor.visitTrigger(this);
  }

  public String toString() {
    StringBuffer sb = new StringBuffer();

    for (int i = 0; i < expressions.length; i++) {
      if (i > 0) {
        sb.append(", ");
      }
      sb.append(expressions[i]);
    }

    return sb.toString();
  }
}
