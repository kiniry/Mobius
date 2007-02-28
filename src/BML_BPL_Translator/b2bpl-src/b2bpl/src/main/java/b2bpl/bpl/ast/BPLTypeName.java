package b2bpl.bpl.ast;

import b2bpl.bpl.BPLVisitor;


public class BPLTypeName extends BPLType {

  private final String name;

  public BPLTypeName(String name) {
    this.name = name;
  }

  public String getName() {
    return name;
  }

  public boolean isTypeName() {
    return true;
  }

  public <R> R accept(BPLVisitor<R> visitor) {
    return visitor.visitTypeName(this);
  }

  public String toString() {
    return name;
  }
}
