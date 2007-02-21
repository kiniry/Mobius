package b2bpl.bytecode.bml.ast;


public abstract class BMLPredicateClause extends BMLSpecificationClause {

  protected final BMLPredicate predicate;

  public BMLPredicateClause(BMLPredicate predicate) {
    this.predicate = predicate;
  }

  public BMLPredicate getPredicate() {
    return predicate;
  }
}
