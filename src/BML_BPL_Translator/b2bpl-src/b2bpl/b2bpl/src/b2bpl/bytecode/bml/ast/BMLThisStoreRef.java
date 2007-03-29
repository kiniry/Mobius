package b2bpl.bytecode.bml.ast;

import b2bpl.bytecode.bml.BMLStoreRefVisitor;


public class BMLThisStoreRef extends BMLStoreRefExpression {

  public static final BMLThisStoreRef THIS = new BMLThisStoreRef();

  private BMLThisStoreRef() {
    // hide the constructor
  }

  public String toString() {
    return "this";
  }

  public <R> R accept(BMLStoreRefVisitor<R> visitor) {
    return visitor.visitThisStoreRef(this);
  }
}
