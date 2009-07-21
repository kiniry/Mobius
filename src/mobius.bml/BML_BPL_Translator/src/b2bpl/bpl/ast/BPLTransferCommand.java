package b2bpl.bpl.ast;


public abstract class BPLTransferCommand extends BPLCommentableNode {

  public String[] getTargetLabels() {
    return new String[0];
  }
}
