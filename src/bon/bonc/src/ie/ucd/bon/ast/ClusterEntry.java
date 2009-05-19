
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.ast.AstNode;

public class ClusterEntry extends AstNode {



  private final String name;
  private final String description;

private final SourceLocation location;

  // === Constructors and Factories ===
  protected ClusterEntry(String name, String description) {
    this(name,description, null);    
  }

  protected ClusterEntry(String name, String description, SourceLocation location) {
    
    assert location != null;
    this.location = location;
    this.name = name; assert name != null;
    this.description = description; assert description != null;
    
  }
  
  public static ClusterEntry mk(String name, String description) {
    return new ClusterEntry(name, description);
  }

  public static ClusterEntry mk(String name, String description, SourceLocation location) {
    return new ClusterEntry(name, description, location);
  }

  // === Accessors ===

  public String getName() { return name; }
  public String getDescription() { return description; }

  // === Others ===
  @Override
  public ClusterEntry clone() {
    String newName = name;
    String newDescription = description;
    
    return ClusterEntry.mk(newName, newDescription, location);
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("ClusterEntry ast node: ");
    
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

