package b2bpl.bytecode.bml.ast;

import b2bpl.bytecode.bml.IBMLStoreRefVisitor;


public class BMLNothingStoreRef extends BMLStoreRef {

  public static final BMLNothingStoreRef NOTHING = new BMLNothingStoreRef();

  private BMLNothingStoreRef() {
    // hide the constructor
  }

  public <R> R accept(IBMLStoreRefVisitor<R> visitor) {
    return visitor.visitNothingStoreRef(this);
  }

  public String toString() {
    return "\\nothing";
  }
}
