package b2bpl.bpl.ast;

import b2bpl.bpl.IBPLVisitor;


public class BPLProgram extends BPLNode {

  private final BPLDeclaration[] declarations;

  public BPLProgram(BPLDeclaration[] declarations) {
    this.declarations = declarations;
  }

  public BPLDeclaration[] getDeclarations() {
    return declarations;
  }

  public <R> R accept(IBPLVisitor<R> visitor) {
    return visitor.visitProgram(this);
  }

  public String toString() {
    StringBuffer sb = new StringBuffer();

    for (BPLDeclaration declaration : declarations) {
      sb.append(declaration);
      sb.append(System.getProperty("line.separator"));
      sb.append(System.getProperty("line.separator"));
    }

    return sb.toString();
  }
}
