package b2bpl.bytecode.bml.ast;

import b2bpl.bytecode.bml.IBMLStoreRefVisitor;


public class BMLLocalVariableStoreRef extends BMLStoreRefExpression {

  private final int index;

  public BMLLocalVariableStoreRef(int index) {
    this.index = index;
  }

  public int getIndex() {
    return index;
  }

  public <R> R accept(IBMLStoreRefVisitor<R> visitor) {
    return visitor.visitLocalVariableStoreRef(this);
  }

  public String toString() {
    return "\\lv(" + index + ")";
  }
}
