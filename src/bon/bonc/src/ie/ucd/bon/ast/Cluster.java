
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.ast.AstNode;

public class Cluster extends StaticComponent {



  private final String name;
  private final List<StaticComponent> components;
  private final Boolean reused;
  private final String comment;

  private final SourceLocation location;

  // === Constructors and Factories ===
  protected Cluster(String name, List<StaticComponent> components, Boolean reused, String comment) {
    this(name,components,reused,comment, null);    
  }

  protected Cluster(String name, List<StaticComponent> components, Boolean reused, String comment, SourceLocation location) {
    
    assert location != null;
    this.location = location;
    this.name = name; assert name != null;
    this.components = components; assert components != null;
    this.reused = reused; assert reused != null;
    this.comment = comment; 
    
  }
  
  public static Cluster mk(String name, List<StaticComponent> components, Boolean reused, String comment) {
    return new Cluster(name, components, reused, comment);
  }

  public static Cluster mk(String name, List<StaticComponent> components, Boolean reused, String comment, SourceLocation location) {
    return new Cluster(name, components, reused, comment, location);
  }
  
  public SourceLocation getLocation() {
    return location;
  }

  // === Accessors ===

  public String getName() { return name; }
  public List<StaticComponent> getComponents() { return components; }
  public Boolean getReused() { return reused; }
  public String getComment() { return comment; }

  // === Others ===
  @Override
  public Cluster clone() {
    String newName = name;
    List<StaticComponent> newComponents = components;
    Boolean newReused = reused;
    String newComment = comment;
    
    return Cluster.mk(newName, newComponents, newReused, newComment, location);
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("Cluster ast node: ");
    
    sb.append("name = ");
    sb.append(name);
    sb.append(", ");
    
    sb.append("components = ");
    sb.append(components);
    sb.append(", ");
    
    sb.append("reused = ");
    sb.append(reused);
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

