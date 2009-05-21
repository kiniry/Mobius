
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.ast.AstNode;

public class DynamicDiagram extends SpecificationElement {



  private final List<DynamicComponent> components;
  private final String extendedId;
  private final String comment;

  private final SourceLocation location;

  // === Constructors and Factories ===
  protected DynamicDiagram(List<DynamicComponent> components, String extendedId, String comment) {
    this(components,extendedId,comment, null);    
  }

  protected DynamicDiagram(List<DynamicComponent> components, String extendedId, String comment, SourceLocation location) {
    
    assert location != null;
    this.location = location;
    this.components = components; assert components != null;
    this.extendedId = extendedId; 
    this.comment = comment; 
    
  }
  
  public static DynamicDiagram mk(List<DynamicComponent> components, String extendedId, String comment) {
    return new DynamicDiagram(components, extendedId, comment);
  }

  public static DynamicDiagram mk(List<DynamicComponent> components, String extendedId, String comment, SourceLocation location) {
    return new DynamicDiagram(components, extendedId, comment, location);
  }
  
  public SourceLocation getLocation() {
    return location;
  }

  // === Accessors ===

  public List<DynamicComponent> getComponents() { return components; }
  public String getExtendedId() { return extendedId; }
  public String getComment() { return comment; }

  // === Others ===
  @Override
  public DynamicDiagram clone() {
    List<DynamicComponent> newComponents = components;
    String newExtendedId = extendedId;
    String newComment = comment;
    
    return DynamicDiagram.mk(newComponents, newExtendedId, newComment, location);
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("DynamicDiagram ast node: ");
    
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

