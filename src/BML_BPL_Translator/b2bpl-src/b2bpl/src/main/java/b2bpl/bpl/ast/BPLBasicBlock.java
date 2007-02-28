package b2bpl.bpl.ast;

import b2bpl.bpl.BPLVisitor;


public class BPLBasicBlock extends BPLCommentableNode {

  private final String label;

  private final BPLCommand[] commands;

  private final BPLTransferCommand transferCommand;

  public BPLBasicBlock(
      String label,
      BPLCommand[] commands,
      BPLTransferCommand transferCommand) {
    this.label = label;
    this.commands = commands;
    this.transferCommand = transferCommand;
  }

  public String getLabel() {
    return label;
  }

  public BPLCommand[] getCommands() {
    return commands;
  }

  public BPLTransferCommand getTransferCommand() {
    return transferCommand;
  }

  public <R> R accept(BPLVisitor<R> visitor) {
    return visitor.visitBasicBlock(this);
  }

  public String toString() {
    StringBuffer sb = new StringBuffer();

    sb.append(label);
    sb.append(':');
    sb.append(System.getProperty("line.separator"));
    for (int i = 0; i < commands.length; i++) {
      sb.append("  ");
      sb.append(commands[i]);
      sb.append(System.getProperty("line.separator"));
    }
    sb.append("  ");
    sb.append(transferCommand);
    sb.append(System.getProperty("line.separator"));

    return sb.toString();
  }
}
