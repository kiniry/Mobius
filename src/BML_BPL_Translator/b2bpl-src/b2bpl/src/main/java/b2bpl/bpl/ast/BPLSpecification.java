package b2bpl.bpl.ast;

import b2bpl.bpl.BPLVisitor;


public class BPLSpecification extends BPLNode {

  private final BPLSpecificationClause[] clauses;

  public BPLSpecification(BPLSpecificationClause... clauses) {
    this.clauses = clauses;
  }

  public BPLSpecificationClause[] getClauses() {
    return clauses;
  }

  public <R> R accept(BPLVisitor<R> visitor) {
    return visitor.visitSpecification(this);
  }
}
