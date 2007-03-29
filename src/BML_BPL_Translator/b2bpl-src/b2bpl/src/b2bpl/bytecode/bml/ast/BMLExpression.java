package b2bpl.bytecode.bml.ast;

import b2bpl.bytecode.JType;
import b2bpl.bytecode.bml.BMLExpressionVisitor;


public abstract class BMLExpression {

  private JType type;

  public boolean isPredicate() {
    return false;
  }

  public final JType getType() {
    return type;
  }

  public final void setType(JType type) {
    this.type = type;
  }

  public abstract <R> R accept(BMLExpressionVisitor<R> visitor);
}
