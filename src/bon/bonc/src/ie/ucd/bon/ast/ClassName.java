
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.ast.AstNode;

public class ClassName extends IndirectionElement {



  private final String name;

  private final SourceLocation location;

  // === Constructors and Factories ===
  protected ClassName(String name) {
    this(name, null);    
  }

  protected ClassName(String name, SourceLocation location) {
    
    assert location != null;
    this.location = location;
    this.name = name; assert name != null;
    
  }
  
  public static ClassName mk(String name) {
    return new ClassName(name);
  }

  public static ClassName mk(String name, SourceLocation location) {
    return new ClassName(name, location);
  }
  
  public SourceLocation getLocation() {
    return location;
  }

  // === Accessors ===

  public String getName() { return name; }

  // === Others ===
  @Override
  public ClassName clone() {
    String newName = name;
    
    return ClassName.mk(newName, location);
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("ClassName ast node: ");
    
    sb.append("name = ");
    sb.append(name);
    sb.append(", ");
    
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2,sb.length());
    }
    return sb.toString();
  }
}

