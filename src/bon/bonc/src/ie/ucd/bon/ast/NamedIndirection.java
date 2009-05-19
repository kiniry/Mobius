
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.ast.AstNode;

public class NamedIndirection extends IndirectionElement {



  private final String className;
  private final List<IndirectionElement> indirectionElements;

  private final SourceLocation location;

  // === Constructors and Factories ===
  protected NamedIndirection(String className, List<IndirectionElement> indirectionElements) {
    this(className,indirectionElements, null);    
  }

  protected NamedIndirection(String className, List<IndirectionElement> indirectionElements, SourceLocation location) {
    
    assert location != null;
    this.location = location;
    this.className = className; assert className != null;
    this.indirectionElements = indirectionElements; assert indirectionElements != null;
    
  }
  
  public static NamedIndirection mk(String className, List<IndirectionElement> indirectionElements) {
    return new NamedIndirection(className, indirectionElements);
  }

  public static NamedIndirection mk(String className, List<IndirectionElement> indirectionElements, SourceLocation location) {
    return new NamedIndirection(className, indirectionElements, location);
  }

  // === Accessors ===

  public String getClassName() { return className; }
  public List<IndirectionElement> getIndirectionElements() { return indirectionElements; }

  // === Others ===
  @Override
  public NamedIndirection clone() {
    String newClassName = className;
    List<IndirectionElement> newIndirectionElements = indirectionElements;
    
    return NamedIndirection.mk(newClassName, newIndirectionElements, location);
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("NamedIndirection ast node: ");
    
    sb.append("className = ");
    sb.append(className);
    sb.append(", ");
    
    sb.append("indirectionElements = ");
    sb.append(indirectionElements);
    sb.append(", ");
    
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2,sb.length());
    }
    return sb.toString();
  }
}

