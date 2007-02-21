package b2bpl.bytecode.bml.ast;

import b2bpl.bytecode.bml.BMLStoreRefVisitor;


public class BMLArrayAllStoreRef extends BMLStoreRefExpression {

  private final BMLStoreRef prefix;

  public BMLArrayAllStoreRef(BMLStoreRef prefix) {
    this.prefix = prefix;
  }

  public BMLStoreRef getPrefix() {
    return prefix;
  }

  public <R> R accept(BMLStoreRefVisitor<R> visitor) {
    return visitor.visitArrayAllStoreRef(this);
  }

  public String toString() {
    return prefix + "[*]";
  }
}
