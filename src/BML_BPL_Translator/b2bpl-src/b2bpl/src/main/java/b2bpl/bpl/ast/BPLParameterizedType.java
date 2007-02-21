package b2bpl.bpl.ast;

import b2bpl.bpl.BPLVisitor;


public class BPLParameterizedType extends BPLType {

  private final BPLType type;

  private final BPLType parameterType;

  public BPLParameterizedType(BPLType type, BPLType parameterType) {
    this.type = type;
    this.parameterType = parameterType;
  }

  public BPLType getType() {
    return type;
  }

  public BPLType getParameterType() {
    return parameterType;
  }

  public boolean isParameterizedType() {
    return true;
  }

  public <R> R accept(BPLVisitor<R> visitor) {
    return visitor.visitParameterizedType(this);
  }

  public String toString() {
    return "<" + parameterType + ">" + type;
  }
}
