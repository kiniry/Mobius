
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;

public class ObjectName extends AstNode {


  private final ClassName className;

  private final String extendedId;


  // === Constructors and Factories ===
  protected ObjectName(ClassName className, String extendedId, SourceLocation location) {
    super(location);
    this.className = className; assert className != null;
    this.extendedId = extendedId; 
    
  }
  
  public static ObjectName mk(ClassName className, String extendedId, SourceLocation location) {
    return new ObjectName(className, extendedId, location);
  }

  // === Accessors ===

  public ClassName getClassName() { return className; }
  public String getExtendedId() { return extendedId; }

  // === Visitor ===
  public void accept(IVisitor visitor) {
    visitor.visitObjectName(this, className, extendedId, getLocation());
  }

  // === Others ===
  @Override
  public ObjectName clone() {
    ClassName newClassName = className == null ? null : className.clone();
    String newExtendedId = extendedId;
    
    return ObjectName.mk(newClassName, newExtendedId, getLocation());
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("ObjectName ast node: ");
    
    sb.append("className = ");
    sb.append(className);
    sb.append(", ");
    
    sb.append("extendedId = ");
    sb.append(extendedId);
    sb.append(", ");
    
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2,sb.length());
    }
    return sb.toString();
  }
}

