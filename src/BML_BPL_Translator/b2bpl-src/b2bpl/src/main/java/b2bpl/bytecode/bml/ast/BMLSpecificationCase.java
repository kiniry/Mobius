package b2bpl.bytecode.bml.ast;


public class BMLSpecificationCase extends BMLNode {

  private final BMLRequiresClause requires;

  private final BMLModifiesClause modifies;

  private final BMLEnsuresClause ensures;

  private final BMLExsuresClause[] exsures;

  public BMLSpecificationCase(
      BMLRequiresClause requires,
      BMLModifiesClause modifies,
      BMLEnsuresClause ensures,
      BMLExsuresClause[] exsures) {
    this.requires = requires;
    this.modifies = modifies;
    this.ensures = ensures;
    this.exsures = exsures;
  }

  public BMLRequiresClause getRequires() {
    return requires;
  }

  public BMLModifiesClause getModifies() {
    return modifies;
  }

  public BMLEnsuresClause getEnsures() {
    return ensures;
  }

  public BMLExsuresClause[] getExsures() {
    return exsures;
  }

  public String toString() {
    StringBuffer sb = new StringBuffer();

    sb.append(requires);
    sb.append(System.getProperty("line.separator"));
    sb.append(modifies);
    sb.append(System.getProperty("line.separator"));
    sb.append(ensures);
    sb.append(System.getProperty("line.separator"));
    for (BMLExsuresClause ex : exsures) {
      sb.append(ex);
      sb.append(System.getProperty("line.separator"));
    }

    return sb.toString();
  }
}
