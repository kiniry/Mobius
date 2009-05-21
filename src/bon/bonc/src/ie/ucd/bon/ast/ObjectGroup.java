
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.ast.AstNode;

public class ObjectGroup extends DynamicComponent {
  public static enum Nameless {
    NOTNAMELESS, 
    NAMELESS
  }


  private final Nameless nameless;
  private final String name;
  private final List<DynamicComponent> components;
  private final String comment;

  private final SourceLocation location;

  // === Constructors and Factories ===
  protected ObjectGroup(Nameless nameless, String name, List<DynamicComponent> components, String comment) {
    this(nameless,name,components,comment, null);    
  }

  protected ObjectGroup(Nameless nameless, String name, List<DynamicComponent> components, String comment, SourceLocation location) {
    
    assert location != null;
    this.location = location;
    this.nameless = nameless; 
    this.name = name; assert name != null;
    this.components = components; assert components != null;
    this.comment = comment; 
    
  }
  
  public static ObjectGroup mk(Nameless nameless, String name, List<DynamicComponent> components, String comment) {
    return new ObjectGroup(nameless, name, components, comment);
  }

  public static ObjectGroup mk(Nameless nameless, String name, List<DynamicComponent> components, String comment, SourceLocation location) {
    return new ObjectGroup(nameless, name, components, comment, location);
  }
  
  public SourceLocation getLocation() {
    return location;
  }

  // === Accessors ===

  public Nameless getNameless() { return nameless; }
  public String getName() { return name; }
  public List<DynamicComponent> getComponents() { return components; }
  public String getComment() { return comment; }

  // === Others ===
  @Override
  public ObjectGroup clone() {
    Nameless newNameless = nameless;
    String newName = name;
    List<DynamicComponent> newComponents = components;
    String newComment = comment;
    
    return ObjectGroup.mk(newNameless, newName, newComponents, newComment, location);
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("ObjectGroup ast node: ");
    
    sb.append("nameless = ");
    sb.append(nameless);
    sb.append(", ");
    
    sb.append("name = ");
    sb.append(name);
    sb.append(", ");
    
    sb.append("components = ");
    sb.append(components);
    sb.append(", ");
    
    sb.append("comment = ");
    sb.append(comment);
    sb.append(", ");
    
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2,sb.length());
    }
    return sb.toString();
  }
}

