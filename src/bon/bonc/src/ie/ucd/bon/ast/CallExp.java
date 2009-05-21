
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;

public class CallExp extends Expression {


  private final Expression qualifier;

  private final List<UnqualifiedCall> callChain;


  // === Constructors and Factories ===
  protected CallExp(Expression qualifier, List<UnqualifiedCall> callChain, SourceLocation location) {
    super(location);
    this.qualifier = qualifier; 
    this.callChain = callChain; assert callChain != null;
    
  }
  
  public static CallExp mk(Expression qualifier, List<UnqualifiedCall> callChain, SourceLocation location) {
    return new CallExp(qualifier, callChain, location);
  }

  // === Accessors ===

  public Expression getQualifier() { return qualifier; }
  public List<UnqualifiedCall> getCallChain() { return callChain; }

  // === Visitor ===
  public void accept(IVisitor visitor) {
    visitor.visitCallExp(this);
  }

  // === Others ===
  @Override
  public CallExp clone() {
    Expression newQualifier = qualifier == null ? null : qualifier.clone();
    List<UnqualifiedCall> newCallChain = callChain;
    
    return CallExp.mk(newQualifier, newCallChain, getLocation());
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("CallExp ast node: ");
    
    sb.append("qualifier = ");
    sb.append(qualifier);
    sb.append(", ");
    
    sb.append("callChain = ");
    sb.append(callChain);
    sb.append(", ");
    
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2,sb.length());
    }
    return sb.toString();
  }
}

