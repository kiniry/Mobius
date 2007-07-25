package b2bpl.bpl.ast;

import b2bpl.bpl.IBPLVisitor;


public class BPLReturnCommand extends BPLTransferCommand {

  public <R> R accept(IBPLVisitor<R> visitor) {
    return visitor.visitReturnCommand(this);
  }

  public String toString() {
    return "return;";
  }
}
