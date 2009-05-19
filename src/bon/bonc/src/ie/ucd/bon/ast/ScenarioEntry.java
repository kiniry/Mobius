
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.ast.AstNode;

public class ScenarioEntry extends AstNode {



  private final String name;
  private final String description;

private final SourceLocation location;

  // === Constructors and Factories ===
  protected ScenarioEntry(String name, String description) {
    this(name,description, null);    
  }

  protected ScenarioEntry(String name, String description, SourceLocation location) {
    
    assert location != null;
    this.location = location;
    this.name = name; assert name != null;
    this.description = description; assert description != null;
    
  }
  
  public static ScenarioEntry mk(String name, String description) {
    return new ScenarioEntry(name, description);
  }

  public static ScenarioEntry mk(String name, String description, SourceLocation location) {
    return new ScenarioEntry(name, description, location);
  }

  // === Accessors ===

  public String getName() { return name; }
  public String getDescription() { return description; }

  // === Others ===
  @Override
  public ScenarioEntry clone() {
    String newName = name;
    String newDescription = description;
    
    return ScenarioEntry.mk(newName, newDescription, location);
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("ScenarioEntry ast node: ");
    
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

