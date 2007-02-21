package b2bpl.bpl.ast;

import b2bpl.bpl.BPLVisitor;


public class BPLAssignmentCommand extends BPLCommand {

  private final BPLExpression left;

  private final BPLExpression right;

  public BPLAssignmentCommand(BPLExpression left, BPLExpression right) {
    this.left = left;
    this.right = right;
  }

  public BPLExpression getLeft() {
    return left;
  }

  public BPLExpression getRight() {
    return right;
  }

  public boolean isPassive() {
    return false;
  }

  public <R> R accept(BPLVisitor<R> visitor) {
    return visitor.visitAssignmentCommand(this);
  }

  public String toString() {
    return left + " := " + right + ";";
  }
}
