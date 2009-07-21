package b2bpl.bpl.ast;

import b2bpl.bpl.IBPLVisitor;


public abstract class BPLNode {

  public abstract <R> R accept(IBPLVisitor<R> visitor);
}
