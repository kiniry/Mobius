package b2bpl.bpl.ast;

import b2bpl.bpl.IBPLVisitor;


public class BPLIntLiteral extends BPLLiteral {

  private final int value;

  public BPLIntLiteral(int value) {
    this.value = value;
  }

  public int getValue() {
    return value;
  }

  public <R> R accept(IBPLVisitor<R> visitor) {
    return visitor.visitIntLiteral(this);
  }

  public String toString() {
    return String.valueOf(value);
  }
}
