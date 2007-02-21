package b2bpl.bytecode.bml.ast;

import b2bpl.bytecode.bml.BMLStoreRefVisitor;


public class BMLSuperStoreRef extends BMLStoreRefExpression {

  public static final BMLSuperStoreRef SUPER = new BMLSuperStoreRef();

  private BMLSuperStoreRef() {
    // hide the constructor
  }

  public String toString() {
    return "super";
  }

  public <R> R accept(BMLStoreRefVisitor<R> visitor) {
    // TODO[om]: Implement!!!
    return null;
  }
}
