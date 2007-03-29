package b2bpl.bpl.ast;

import b2bpl.bpl.BPLVisitor;


public class BPLGotoCommand extends BPLTransferCommand {

  private final String[] targetLabels;

  public BPLGotoCommand(String... labels) {
    this.targetLabels = labels;
  }

  public String[] getTargetLabels() {
    return targetLabels;
  }

  public <R> R accept(BPLVisitor<R> visitor) {
    return visitor.visitGotoCommand(this);
  }

  public String toString() {
    StringBuffer sb = new StringBuffer();

    sb.append("goto ");
    for (int i = 0; i < targetLabels.length; i++) {
      if (i > 0) {
        sb.append(", ");
      }
      sb.append(targetLabels[i]);
    }
    sb.append(";");

    return sb.toString();
  }
}
