package b2bpl.bpl.ast;


public abstract class BPLType extends BPLNode {

  public boolean isBuiltInType() {
    return false;
  }

  public boolean isTypeName() {
    return false;
  }

  public boolean isArrayType() {
    return false;
  }

  public boolean isParameterizedType() {
    return false;
  }
}
