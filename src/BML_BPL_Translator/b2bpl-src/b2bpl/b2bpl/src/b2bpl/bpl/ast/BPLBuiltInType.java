package b2bpl.bpl.ast;

import b2bpl.bpl.BPLVisitor;


public class BPLBuiltInType extends BPLType {

  public static final BPLBuiltInType BOOL = new BPLBuiltInType("bool");

  public static final BPLBuiltInType INT = new BPLBuiltInType("int");

  public static final BPLBuiltInType REF = new BPLBuiltInType("ref");

  public static final BPLBuiltInType NAME = new BPLBuiltInType("name");

  public static final BPLBuiltInType ANY = new BPLBuiltInType("any");

  private final String name;

  private BPLBuiltInType(String name) {
    this.name = name;
  }

  public String getName() {
    return name;
  }

  public boolean isBuiltInType() {
    return true;
  }

  public <R> R accept(BPLVisitor<R> visitor) {
    return visitor.visitBuiltInType(this);
  }

  public String toString() {
    return name;
  }
}
