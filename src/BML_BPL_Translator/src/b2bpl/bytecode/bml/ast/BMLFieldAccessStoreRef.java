package b2bpl.bytecode.bml.ast;

import b2bpl.bytecode.bml.IBMLStoreRefVisitor;


public class BMLFieldAccessStoreRef extends BMLStoreRefExpression {

  private final BMLStoreRef prefix;

  private final BMLFieldStoreRef field;

  public BMLFieldAccessStoreRef(BMLStoreRef prefix, BMLFieldStoreRef field) {
    this.prefix = prefix;
    this.field = field;
  }

  public BMLStoreRef getPrefix() {
    return prefix;
  }

  public BMLFieldStoreRef getField() {
    return field;
  }

  public <R> R accept(IBMLStoreRefVisitor<R> visitor) {
    return visitor.visitFieldAccessStoreRef(this);
  }

  public String toString() {
    return prefix + "." + field;
  }
}
