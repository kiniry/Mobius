
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.ast.AstNode;

public class GenericIndirection extends AstNode {



  private final String indirectionElement;

  private final SourceLocation location;

  // === Constructors and Factories ===
  protected GenericIndirection(String indirectionElement) {
    this(indirectionElement, null);    
  }

  protected GenericIndirection(String indirectionElement, SourceLocation location) {
    
    assert location != null;
    this.location = location;
    this.indirectionElement = indirectionElement; assert indirectionElement != null;
    
  }
  
  public static GenericIndirection mk(String indirectionElement) {
    return new GenericIndirection(indirectionElement);
  }

  public static GenericIndirection mk(String indirectionElement, SourceLocation location) {
    return new GenericIndirection(indirectionElement, location);
  }

  // === Accessors ===

  public String getIndirectionElement() { return indirectionElement; }

  // === Others ===
  @Override
  public GenericIndirection clone() {
    String newIndirectionElement = indirectionElement;
    
    return GenericIndirection.mk(newIndirectionElement, location);
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("GenericIndirection ast node: ");
    
    sb.append("indirectionElement = ");
    sb.append(indirectionElement);
    sb.append(", ");
    
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2,sb.length());
    }
    return sb.toString();
  }
}

