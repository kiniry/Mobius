
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.ast.AstNode;

public class AssertionClause extends AstNode {


  private final Expression expression;


  private final SourceLocation location;

  // === Constructors and Factories ===
  protected AssertionClause(Expression expression) {
    this(expression, null);    
  }

  protected AssertionClause(Expression expression, SourceLocation location) {
    
    assert location != null;
    this.location = location;
    this.expression = expression; assert expression != null;
    
  }
  
  public static AssertionClause mk(Expression expression) {
    return new AssertionClause(expression);
  }

  public static AssertionClause mk(Expression expression, SourceLocation location) {
    return new AssertionClause(expression, location);
  }

  // === Accessors ===

  public Expression getExpression() { return expression; }

  // === Others ===
  @Override
  public AssertionClause clone() {
    Expression newExpression = expression == null ? null : expression.clone();
    
    return AssertionClause.mk(newExpression, location);
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("AssertionClause ast node: ");
    
    sb.append("expression = ");
    sb.append(expression);
    sb.append(", ");
    
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2,sb.length());
    }
    return sb.toString();
  }
}

