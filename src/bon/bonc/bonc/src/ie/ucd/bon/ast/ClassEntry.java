
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;

public class ClassEntry extends AstNode {



  public final String name;
  public final String description;


  // === Constructors and Factories ===
  protected ClassEntry(String name, String description, SourceLocation location) {
    super(location);
    this.name = name; assert name != null;
    this.description = description; assert description != null;
    
  }
  
  public static ClassEntry mk(String name, String description, SourceLocation location) {
    return new ClassEntry(name, description, location);
  }

  // === Accessors ===

  public String getName() { return name; }
  public String getDescription() { return description; }

  // === Visitor ===
  public void accept(IVisitorWithAdditions visitor) {
    visitor.visitClassEntry(this, name, description, getLocation());
  }

  // === Others ===
  @Override
  public ClassEntry clone() {
    String newName = name;
    String newDescription = description;
    
    return ClassEntry.mk(newName, newDescription, getLocation());
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("ClassEntry ast node: ");
    
    sb.append("name = ");
    sb.append(name);
    sb.append(", ");
    
    sb.append("description = ");
    sb.append(description);
    sb.append(", ");
    
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2,sb.length());
    }
    return sb.toString();
  }
}

