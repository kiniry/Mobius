package b2bpl.bpl.ast;

import b2bpl.bpl.BPLVisitor;


public class BPLImplementationBody extends BPLNode {

  private final BPLVariableDeclaration[] variableDeclarations;

  private final BPLBasicBlock[] basicBlocks;

  public BPLImplementationBody(
      BPLVariableDeclaration[] variableDeclarations,
      BPLBasicBlock[] basicBlocks) {
    this.variableDeclarations = variableDeclarations;
    this.basicBlocks = basicBlocks;
  }

  public BPLVariableDeclaration[] getVariableDeclarations() {
    return variableDeclarations;
  }

  public BPLBasicBlock[] getBasicBlocks() {
    return basicBlocks;
  }

  public <R> R accept(BPLVisitor<R> visitor) {
    return visitor.visitImplementationBody(this);
  }

  public String toString() {
    StringBuffer sb = new StringBuffer();

    for (int i = 0; i < variableDeclarations.length; i++) {
      sb.append("  ");
      sb.append(variableDeclarations[i]);
      sb.append(System.getProperty("line.separator"));
    }
    sb.append(System.getProperty("line.separator"));
    for (int i = 0; i < basicBlocks.length; i++) {
      sb.append(basicBlocks[i]);
      sb.append(System.getProperty("line.separator"));
    }

    return sb.toString();
  }
}
