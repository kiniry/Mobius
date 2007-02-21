package b2bpl.bpl.ast;

import b2bpl.bpl.BPLVisitor;


public abstract class BPLNode {

  public abstract <R> R accept(BPLVisitor<R> visitor);
}
