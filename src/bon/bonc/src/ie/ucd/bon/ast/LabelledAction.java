
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;

public class LabelledAction extends AstNode {



  private final String label;
  private final String description;


  // === Constructors and Factories ===
  protected LabelledAction(String label, String description, SourceLocation location) {
    super(location);
    this.label = label; assert label != null;
    this.description = description; assert description != null;
    
  }
  
  public static LabelledAction mk(String label, String description, SourceLocation location) {
    return new LabelledAction(label, description, location);
  }

  // === Accessors ===

  public String getLabel() { return label; }
  public String getDescription() { return description; }

  // === Visitor ===
  public void accept(IVisitor visitor) {
    visitor.visitLabelledAction(this, label, description);
  }

  // === Others ===
  @Override
  public LabelledAction clone() {
    String newLabel = label;
    String newDescription = description;
    
    return LabelledAction.mk(newLabel, newDescription, getLocation());
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("LabelledAction ast node: ");
    
    sb.append("label = ");
    sb.append(label);
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

