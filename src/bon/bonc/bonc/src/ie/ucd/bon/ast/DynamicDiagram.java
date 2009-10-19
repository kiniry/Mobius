
/**
  This class is generated automatically from normal_classes.tpl.
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;

public class DynamicDiagram extends SpecificationElement {



  public final List<DynamicComponent> components;
  public final String extendedId;
  public final String comment;


  // === Constructors and Factories ===
  protected DynamicDiagram(List<DynamicComponent> components, String extendedId, String comment, SourceLocation location) {
    super(location);
    this.components = components; assert components != null;
    this.extendedId = extendedId; 
    this.comment = comment; 
  }

  public static DynamicDiagram mk(List<DynamicComponent> components, String extendedId, String comment, SourceLocation location) {
    return new DynamicDiagram(components, extendedId, comment, location);
  }

  // === Accessors ===

  public List<DynamicComponent> getComponents() { return components; }
  public String getExtendedId() { return extendedId; }
  public String getComment() { return comment; }

  // === Visitor ===
  public void accept(IVisitorWithAdditions visitor) {
    visitor.visitDynamicDiagram(this, components, extendedId, comment, getLocation());
  }

  // === Others ===
  @Override
  public DynamicDiagram clone() {
    List<DynamicComponent> newComponents = components;
    String newExtendedId = extendedId;
    String newComment = comment;
    return DynamicDiagram.mk(newComponents, newExtendedId, newComment, getLocation());
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
      sb.delete(sb.length()-2, sb.length());
    }
    return sb.toString();
  }
}

