package b2bpl.bpl.ast;

import b2bpl.bpl.BPLVisitor;


public class BPLReturnCommand extends BPLTransferCommand {

  public static final BPLReturnCommand RETURN = new BPLReturnCommand();

  private BPLReturnCommand() {
    // hide the constructor
  }

  public <R> R accept(BPLVisitor<R> visitor) {
    return visitor.visitReturnCommand(this);
  }

  public String toString() {
    return "return;";
  }
}
