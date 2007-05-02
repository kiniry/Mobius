package b2bpl.bpl.ast;

import b2bpl.bpl.IBPLVisitor;


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

  public <R> R accept(IBPLVisitor<R> visitor) {
    return visitor.visitTypeName(this);
  }

  public String toString() {
    return name;
  }
}
