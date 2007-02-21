package b2bpl.bpl.ast;


public abstract class BPLTransferCommand extends BPLNode {

  public String[] getTargetLabels() {
    return new String[0];
  }
}
