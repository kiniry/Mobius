
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;

public class BooleanConstant extends ManifestConstant {



  private final Boolean value;


  // === Constructors and Factories ===
  protected BooleanConstant(Boolean value, SourceLocation location) {
    super(location);
    this.value = value; assert value != null;
    
  }
  
  public static BooleanConstant mk(Boolean value, SourceLocation location) {
    return new BooleanConstant(value, location);
  }

  // === Accessors ===

  public Boolean getValue() { return value; }

  // === Visitor ===
  public void accept(IVisitorWithAdditions visitor) {
    visitor.visitBooleanConstant(this, value, getLocation());
  }

  // === Others ===
  @Override
  public BooleanConstant clone() {
    Boolean newValue = value;
    
    return BooleanConstant.mk(newValue, getLocation());
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("BooleanConstant ast node: ");
    
    sb.append("value = ");
    sb.append(value);
    sb.append(", ");
    
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2,sb.length());
    }
    return sb.toString();
  }
}

