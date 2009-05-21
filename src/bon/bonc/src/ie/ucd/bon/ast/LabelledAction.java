
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.ast.AstNode;

public class LabelledAction extends AstNode {



  private final String label;
  private final String description;

  private final SourceLocation location;

  // === Constructors and Factories ===
  protected LabelledAction(String label, String description) {
    this(label,description, null);    
  }

  protected LabelledAction(String label, String description, SourceLocation location) {
    
    assert location != null;
    this.location = location;
    this.label = label; assert label != null;
    this.description = description; assert description != null;
    
  }
  
  public static LabelledAction mk(String label, String description) {
    return new LabelledAction(label, description);
  }

  public static LabelledAction mk(String label, String description, SourceLocation location) {
    return new LabelledAction(label, description, location);
  }
  
  public SourceLocation getLocation() {
    return location;
  }

  // === Accessors ===

  public String getLabel() { return label; }
  public String getDescription() { return description; }

  // === Others ===
  @Override
  public LabelledAction clone() {
    String newLabel = label;
    String newDescription = description;
    
    return LabelledAction.mk(newLabel, newDescription, location);
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

