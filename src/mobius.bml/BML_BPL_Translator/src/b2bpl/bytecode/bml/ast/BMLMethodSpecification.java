package b2bpl.bytecode.bml.ast;


public class BMLMethodSpecification {

  private final BMLRequiresClause requires;

  private final BMLSpecificationCase[] cases;

  public BMLMethodSpecification(
      BMLRequiresClause requires,
      BMLSpecificationCase... cases) {
    this.requires = requires;
    this.cases = cases;
  }

  public BMLRequiresClause getRequires() {
    return requires;
  }

  public BMLSpecificationCase[] getCases() {
    return cases;
  }

  public String toString() {
    StringBuffer sb = new StringBuffer();

    for (int i = 0; i < cases.length; i++) {
      if (i > 0) {
        sb.append("also" + System.getProperty("line.separator"));
      }
      sb.append(cases[i]);
    }

    return sb.toString();
  }
}
