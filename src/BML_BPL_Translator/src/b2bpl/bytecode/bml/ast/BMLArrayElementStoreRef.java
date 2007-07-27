package b2bpl.bytecode.bml.ast;

import b2bpl.bytecode.bml.IBMLStoreRefVisitor;


public class BMLArrayElementStoreRef extends BMLStoreRefExpression {

  private final BMLStoreRef prefix;

  private final BMLExpression index;

  public BMLArrayElementStoreRef(BMLStoreRef prefix, BMLExpression index) {
    this.prefix = prefix;
    this.index = index;
  }

  public BMLStoreRef getPrefix() {
    return prefix;
  }

  public BMLExpression getIndex() {
    return index;
  }

  public <R> R accept(IBMLStoreRefVisitor<R> visitor) {
    return visitor.visitArrayElementStoreRef(this);
  }

  public String toString() {
    return prefix + "[" + index + "]";
  }
}
