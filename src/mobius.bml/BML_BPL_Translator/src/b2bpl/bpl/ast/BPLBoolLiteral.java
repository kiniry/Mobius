package b2bpl.bpl.ast;

import b2bpl.bpl.IBPLVisitor;


public class BPLBoolLiteral extends BPLLiteral {

  public static final BPLBoolLiteral TRUE = new BPLBoolLiteral(true);

  public static final BPLBoolLiteral FALSE = new BPLBoolLiteral(false);

  private final boolean value;

  private BPLBoolLiteral(boolean value) {
    this.value = value;
  }

  public boolean getValue() {
    return value;
  }

  public boolean isPredicate() {
    return true;
  }

  public <R> R accept(IBPLVisitor<R> visitor) {
    return visitor.visitBoolLiteral(this);
  }

  public String toString() {
    return String.valueOf(value);
  }
}
