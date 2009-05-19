
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.ast.AstNode;

public class Invariant extends AstNode {



  private final List<AssertionClause> clauses;

private final SourceLocation location;

  // === Constructors and Factories ===
  protected Invariant(List<AssertionClause> clauses) {
    this(clauses, null);    
  }

  protected Invariant(List<AssertionClause> clauses, SourceLocation location) {
    
    assert location != null;
    this.location = location;
    this.clauses = clauses; assert clauses != null;
    
  }
  
  public static Invariant mk(List<AssertionClause> clauses) {
    return new Invariant(clauses);
  }

  public static Invariant mk(List<AssertionClause> clauses, SourceLocation location) {
    return new Invariant(clauses, location);
  }

  // === Accessors ===

  public List<AssertionClause> getClauses() { return clauses; }

  // === Others ===
  @Override
  public Invariant clone() {
    List<AssertionClause> newClauses = clauses;
    
    return Invariant.mk(newClauses, location);
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("Invariant ast node: ");
    
    sb.append("clauses = ");
    sb.append(clauses);
    sb.append(", ");
    
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2,sb.length());
    }
    return sb.toString();
  }
}

