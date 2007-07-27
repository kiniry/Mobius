package b2bpl.bpl.ast;

import b2bpl.bpl.IBPLVisitor;


public class BPLNullLiteral extends BPLLiteral {

  public static final BPLNullLiteral NULL = new BPLNullLiteral();

  private BPLNullLiteral() {
    // hide the constructor
  }

  public <R> R accept(IBPLVisitor<R> visitor) {
    return visitor.visitNullLiteral(this);
  }

  public String toString() {
    return "null";
  }
}
