
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;

public class ClassName extends IndirectionElement {



  private final String name;


  // === Constructors and Factories ===
  protected ClassName(String name, SourceLocation location) {
    super(location);
    this.name = name; assert name != null;
    
  }
  
  public static ClassName mk(String name, SourceLocation location) {
    return new ClassName(name, location);
  }

  // === Accessors ===

  public String getName() { return name; }

  // === Visitor ===
  public void accept(IVisitor visitor) {
    visitor.visitClassName(this, name, getLocation());
  }

  // === Others ===
  @Override
  public ClassName clone() {
    String newName = name;
    
    return ClassName.mk(newName, getLocation());
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

