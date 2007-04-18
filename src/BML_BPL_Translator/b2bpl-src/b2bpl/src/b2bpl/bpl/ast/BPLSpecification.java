package b2bpl.bpl.ast;

import java.util.ArrayList;
import java.util.List;

import b2bpl.bpl.BPLVisitor;


public class BPLSpecification extends BPLNode {

  private final BPLSpecificationClause[] clauses;

  public BPLSpecification(BPLSpecificationClause... clauses) {
    this.clauses = clauses;
  }
  
  public BPLSpecification(BPLRequiresClause[] requiresClauses, BPLModifiesClause[] modifiesClauses, BPLEnsuresClause[] ensuresClauses) {
    List<BPLSpecificationClause> specs = new ArrayList<BPLSpecificationClause>();
    for (BPLRequiresClause r : requiresClauses) { if (r.getExpression() != BPLBoolLiteral.TRUE) specs.add(r); }
    for (BPLModifiesClause m : modifiesClauses) specs.add(m);
    for (BPLEnsuresClause  e : ensuresClauses)  { if (e.getExpression() != BPLBoolLiteral.TRUE) specs.add(e); }
    this.clauses = specs.toArray(new BPLSpecificationClause[specs.size()]);
  }
  
  public BPLSpecificationClause[] getClauses() {
    return clauses;
  }

  public <R> R accept(BPLVisitor<R> visitor) {
    return visitor.visitSpecification(this);
  }
}