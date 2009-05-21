
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.ast.AstNode;

public class ObjectName extends AstNode {



  private final String className;
  private final String extendedId;

  private final SourceLocation location;

  // === Constructors and Factories ===
  protected ObjectName(String className, String extendedId) {
    this(className,extendedId, null);    
  }

  protected ObjectName(String className, String extendedId, SourceLocation location) {
    
    assert location != null;
    this.location = location;
    this.className = className; assert className != null;
    this.extendedId = extendedId; 
    
  }
  
  public static ObjectName mk(String className, String extendedId) {
    return new ObjectName(className, extendedId);
  }

  public static ObjectName mk(String className, String extendedId, SourceLocation location) {
    return new ObjectName(className, extendedId, location);
  }
  
  public SourceLocation getLocation() {
    return location;
  }

  // === Accessors ===

  public String getClassName() { return className; }
  public String getExtendedId() { return extendedId; }

  // === Others ===
  @Override
  public ObjectName clone() {
    String newClassName = className;
    String newExtendedId = extendedId;
    
    return ObjectName.mk(newClassName, newExtendedId, location);
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

