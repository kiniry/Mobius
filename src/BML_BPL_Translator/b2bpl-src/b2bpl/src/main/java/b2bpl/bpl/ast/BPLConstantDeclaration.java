package b2bpl.bpl.ast;

import b2bpl.bpl.BPLVisitor;


public class BPLConstantDeclaration extends BPLDeclaration {

  private final BPLVariable[] constants;

  public BPLConstantDeclaration(BPLVariable... constants) {
    this.constants = constants;
  }

  public BPLVariable[] getConstants() {
    return constants;
  }

  public <R> R accept(BPLVisitor<R> visitor) {
    return visitor.visitConstantDeclaration(this);
  }

  public String toString() {
    StringBuffer sb = new StringBuffer();

    sb.append("const ");
    for (int i = 0; i < constants.length; i++) {
      if (i > 0) {
        sb.append(", ");
      }
      sb.append(constants[i]);
    }
    sb.append(';');

    return sb.toString();
  }
}
