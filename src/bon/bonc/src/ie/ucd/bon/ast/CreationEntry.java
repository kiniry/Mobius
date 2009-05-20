
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.ast.AstNode;

public class CreationEntry extends AstNode {



  private final String name;
  private final List<String> types;

  private final SourceLocation location;

  // === Constructors and Factories ===
  protected CreationEntry(String name, List<String> types) {
    this(name,types, null);    
  }

  protected CreationEntry(String name, List<String> types, SourceLocation location) {
    
    assert location != null;
    this.location = location;
    this.name = name; assert name != null;
    this.types = types; assert types != null;
    
  }
  
  public static CreationEntry mk(String name, List<String> types) {
    return new CreationEntry(name, types);
  }

  public static CreationEntry mk(String name, List<String> types, SourceLocation location) {
    return new CreationEntry(name, types, location);
  }
  
  public SourceLocation getLocation() {
    return location;
  }

  // === Accessors ===

  public String getName() { return name; }
  public List<String> getTypes() { return types; }

  // === Others ===
  @Override
  public CreationEntry clone() {
    String newName = name;
    List<String> newTypes = types;
    
    return CreationEntry.mk(newName, newTypes, location);
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("CreationEntry ast node: ");
    
    sb.append("name = ");
    sb.append(name);
    sb.append(", ");
    
    sb.append("types = ");
    sb.append(types);
    sb.append(", ");
    
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2,sb.length());
    }
    return sb.toString();
  }
}

