package b2bpl.bytecode.bml.ast;


public class BMLEnsuresClause extends BMLPredicateClause {

  public BMLEnsuresClause(BMLPredicate predicate) {
    super(predicate);
  }

  public String toString() {
    return "ensures " + predicate + ";";
  }
}
