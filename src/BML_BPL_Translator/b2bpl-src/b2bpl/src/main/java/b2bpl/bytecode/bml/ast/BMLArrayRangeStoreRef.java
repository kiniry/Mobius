package b2bpl.bytecode.bml.ast;

import b2bpl.bytecode.bml.BMLStoreRefVisitor;


public class BMLArrayRangeStoreRef extends BMLStoreRefExpression {

  private final BMLStoreRef prefix;

  private final BMLExpression startIndex;

  private final BMLExpression endIndex;

  public BMLArrayRangeStoreRef(
      BMLStoreRef prefix,
      BMLExpression startIndex,
      BMLExpression endIndex) {
    this.prefix = prefix;
    this.startIndex = startIndex;
    this.endIndex = endIndex;
  }

  public BMLStoreRef getPrefix() {
    return prefix;
  }

  public BMLExpression getStartIndex() {
    return startIndex;
  }

  public BMLExpression getEndIndex() {
    return endIndex;
  }

  public <R> R accept(BMLStoreRefVisitor<R> visitor) {
    return visitor.visitArrayRangeStoreRef(this);
  }

  public String toString() {
    return prefix + "[" + startIndex + " .. " + endIndex + "]";
  }
}
