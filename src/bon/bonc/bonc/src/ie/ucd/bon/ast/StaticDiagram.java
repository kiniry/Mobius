
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;

public class StaticDiagram extends SpecificationElement {



  private final List<StaticComponent> components;
  private final String extendedId;
  private final String comment;


  // === Constructors and Factories ===
  protected StaticDiagram(List<StaticComponent> components, String extendedId, String comment, SourceLocation location) {
    super(location);
    this.components = components; assert components != null;
    this.extendedId = extendedId; 
    this.comment = comment; 
    
  }
  
  public static StaticDiagram mk(List<StaticComponent> components, String extendedId, String comment, SourceLocation location) {
    return new StaticDiagram(components, extendedId, comment, location);
  }

  // === Accessors ===

  public List<StaticComponent> getComponents() { return components; }
  public String getExtendedId() { return extendedId; }
  public String getComment() { return comment; }

  // === Visitor ===
  public void accept(IVisitorWithAdditions visitor) {
    visitor.visitStaticDiagram(this, components, extendedId, comment, getLocation());
  }

  // === Others ===
  @Override
  public StaticDiagram clone() {
    List<StaticComponent> newComponents = components;
    String newExtendedId = extendedId;
    String newComment = comment;
    
    return StaticDiagram.mk(newComponents, newExtendedId, newComment, getLocation());
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("StaticDiagram ast node: ");
    
    sb.append("components = ");
    sb.append(components);
    sb.append(", ");
    
    sb.append("extendedId = ");
    sb.append(extendedId);
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

