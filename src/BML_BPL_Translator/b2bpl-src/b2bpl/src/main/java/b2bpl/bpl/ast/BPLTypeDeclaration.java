package b2bpl.bpl.ast;

import b2bpl.bpl.BPLVisitor;


public class BPLTypeDeclaration extends BPLDeclaration {

  private final String[] typeNames;

  public BPLTypeDeclaration(String... typeNames) {
    this.typeNames = typeNames;
  }

  public String[] getTypeNames() {
    return typeNames;
  }

  public <R> R accept(BPLVisitor<R> visitor) {
    return visitor.visitTypeDeclaration(this);
  }

  public String toString() {
    StringBuffer sb = new StringBuffer();

    sb.append("type ");
    for (int i = 0; i < typeNames.length; i++) {
      if (i > 0) {
        sb.append(", ");
      }
      sb.append(typeNames[i]);
    }
    sb.append(';');

    return sb.toString();
  }
}
