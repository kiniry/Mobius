package b2bpl.bytecode.bml.ast;


public class BMLAssumeStatement {

  private final BMLPredicate predicate;

  public BMLAssumeStatement(BMLPredicate predicate) {
    this.predicate = predicate;
  }

  public BMLPredicate getPredicate() {
    return predicate;
  }

  public String toString() {
    return "assume " + predicate + ";";
  }
}
