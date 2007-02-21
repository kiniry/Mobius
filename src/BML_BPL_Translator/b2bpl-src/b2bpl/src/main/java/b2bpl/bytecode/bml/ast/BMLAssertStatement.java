package b2bpl.bytecode.bml.ast;


public class BMLAssertStatement extends BMLNode {

  private final BMLPredicate predicate;

  public BMLAssertStatement(BMLPredicate predicate) {
    this.predicate = predicate;
  }

  public BMLPredicate getPredicate() {
    return predicate;
  }

  public String toString() {
    return "assert " + predicate + ";";
  }
}
