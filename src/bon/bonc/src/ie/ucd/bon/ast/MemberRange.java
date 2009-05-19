
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.ast.AstNode;

public class MemberRange extends VariableRange {


  private final Expression expression;

  private final List<String> identifiers;

private final SourceLocation location;

  // === Constructors and Factories ===
  protected MemberRange(List<String> identifiers, Expression expression) {
    this(identifiers,expression, null);    
  }

  protected MemberRange(List<String> identifiers, Expression expression, SourceLocation location) {
    
    assert location != null;
    this.location = location;
    this.identifiers = identifiers; assert identifiers != null;
    this.expression = expression; assert expression != null;
    
  }
  
  public static MemberRange mk(List<String> identifiers, Expression expression) {
    return new MemberRange(identifiers, expression);
  }

  public static MemberRange mk(List<String> identifiers, Expression expression, SourceLocation location) {
    return new MemberRange(identifiers, expression, location);
  }

  // === Accessors ===

  public List<String> getIdentifiers() { return identifiers; }
  public Expression getExpression() { return expression; }

  // === Others ===
  @Override
  public MemberRange clone() {
    List<String> newIdentifiers = identifiers;
    Expression newExpression = expression == null ? null : expression.clone();
    
    return MemberRange.mk(newIdentifiers, newExpression, location);
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("MemberRange ast node: ");
    
    sb.append("identifiers = ");
    sb.append(identifiers);
    sb.append(", ");
    
    sb.append("expression = ");
    sb.append(expression);
    sb.append(", ");
    
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2,sb.length());
    }
    return sb.toString();
  }
}

