package b2bpl.bytecode.bml.ast;

import b2bpl.bytecode.bml.BMLStoreRefVisitor;


public class BMLLocalVariableStoreRef extends BMLStoreRefExpression {

  private final int index;

  public BMLLocalVariableStoreRef(int index) {
    this.index = index;
  }

  public int getIndex() {
    return index;
  }

  public <R> R accept(BMLStoreRefVisitor<R> visitor) {
    return visitor.visitLocalVariableStoreRef(this);
  }

  public String toString() {
    return "\\lv(" + index + ")";
  }
}
