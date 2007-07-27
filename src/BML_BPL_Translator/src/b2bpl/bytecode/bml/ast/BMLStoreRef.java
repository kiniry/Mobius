package b2bpl.bytecode.bml.ast;

import b2bpl.bytecode.bml.IBMLStoreRefVisitor;


public abstract class BMLStoreRef {

  public static final BMLStoreRef[] EMPTY_ARRAY = new BMLStoreRef[0];

  public abstract <R> R accept(IBMLStoreRefVisitor<R> visitor);
}
