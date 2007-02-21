package b2bpl.bytecode.bml.ast;

import b2bpl.bytecode.bml.BMLStoreRefVisitor;


public class BMLEverythingStoreRef extends BMLStoreRef {

  public static final BMLEverythingStoreRef EVERYTHING =
    new BMLEverythingStoreRef();

  private BMLEverythingStoreRef() {
    // hide the constructor
  }

  public <R> R accept(BMLStoreRefVisitor<R> visitor) {
    return visitor.visitEverythingStoreRef(this);
  }

  public String toString() {
    return "\\everything";
  }
}
