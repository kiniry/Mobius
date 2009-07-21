
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;

public class StaticRefPart extends AstNode {



  private final String name;


  // === Constructors and Factories ===
  protected StaticRefPart(String name, SourceLocation location) {
    super(location);
    this.name = name; assert name != null;
    
  }
  
  public static StaticRefPart mk(String name, SourceLocation location) {
    return new StaticRefPart(name, location);
  }

  // === Accessors ===

  public String getName() { return name; }

  // === Visitor ===
  public void accept(IVisitor visitor) {
    visitor.visitStaticRefPart(this, name, getLocation());
  }

  // === Others ===
  @Override
  public StaticRefPart clone() {
    String newName = name;
    
    return StaticRefPart.mk(newName, getLocation());
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("StaticRefPart ast node: ");
    
    sb.append("name = ");
    sb.append(name);
    sb.append(", ");
    
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2,sb.length());
    }
    return sb.toString();
  }
}

