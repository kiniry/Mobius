package b2bpl.bpl.ast;

import b2bpl.bpl.BPLVisitor;


public class BPLFunctionParameter extends BPLNode {

  private final String name;

  private final BPLType type;

  public BPLFunctionParameter(BPLType type) {
    this(null, type);
  }

  public BPLFunctionParameter(String name, BPLType type) {
    this.name = name;
    this.type = type;
  }

  public String getName() {
    return name;
  }

  public BPLType getType() {
    return type;
  }

  public <R> R accept(BPLVisitor<R> visitor) {
    return visitor.visitFunctionParameter(this);
  }

  public String toString() {
    StringBuffer sb = new StringBuffer();

    if (name != null) {
      sb.append(name);
      sb.append(": ");
    }
    sb.append(type);

    return sb.toString();
  }
}
