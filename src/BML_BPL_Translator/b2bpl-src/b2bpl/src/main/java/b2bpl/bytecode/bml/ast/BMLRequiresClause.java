package b2bpl.bytecode.bml.ast;


public class BMLRequiresClause extends BMLPredicateClause {

  public BMLRequiresClause(BMLPredicate predicate) {
    super(predicate);
  }

  public String toString() {
    return "requires " + predicate + ";";
  }
}
