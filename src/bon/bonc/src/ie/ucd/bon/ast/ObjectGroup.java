
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;

public class ObjectGroup extends DynamicComponent {
  public static enum Nameless {
    NOTNAMELESS, 
    NAMELESS
  }


  private final Nameless nameless;
  private final String name;
  private final List<DynamicComponent> components;
  private final String comment;


  // === Constructors and Factories ===
  protected ObjectGroup(Nameless nameless, String name, List<DynamicComponent> components, String comment, SourceLocation location) {
    super(location);
    this.nameless = nameless; 
    this.name = name; assert name != null;
    this.components = components; assert components != null;
    this.comment = comment; 
    
  }
  
  public static ObjectGroup mk(Nameless nameless, String name, List<DynamicComponent> components, String comment, SourceLocation location) {
    return new ObjectGroup(nameless, name, components, comment, location);
  }

  // === Accessors ===

  public Nameless getNameless() { return nameless; }
  public String getName() { return name; }
  public List<DynamicComponent> getComponents() { return components; }
  public String getComment() { return comment; }

  // === Visitor ===
  public void accept(IVisitor visitor) {
    visitor.visitObjectGroup(this);
  }

  // === Others ===
  @Override
  public ObjectGroup clone() {
    Nameless newNameless = nameless;
    String newName = name;
    List<DynamicComponent> newComponents = components;
    String newComment = comment;
    
    return ObjectGroup.mk(newNameless, newName, newComponents, newComment, getLocation());
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

