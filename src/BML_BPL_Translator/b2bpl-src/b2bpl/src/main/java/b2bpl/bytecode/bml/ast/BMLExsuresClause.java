package b2bpl.bytecode.bml.ast;

import b2bpl.bytecode.JType;


public class BMLExsuresClause extends BMLPredicateClause {

  public static final BMLExsuresClause[] EMPTY_ARRAY = new BMLExsuresClause[0];

  private final JType exceptionType;

  public BMLExsuresClause(JType exceptionType, BMLPredicate predicate) {
    super(predicate);
    this.exceptionType = exceptionType;
  }

  public JType getExceptionType() {
    return exceptionType;
  }

  public String toString() {
    return "exsures " + exceptionType.getName() + " " + predicate + ";";
  }
}
