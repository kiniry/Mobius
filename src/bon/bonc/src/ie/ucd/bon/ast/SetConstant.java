
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;

public class SetConstant extends ManifestConstant {



  private final List<EnumerationElement> enumerations;


  // === Constructors and Factories ===
  protected SetConstant(List<EnumerationElement> enumerations, SourceLocation location) {
    super(location);
    this.enumerations = enumerations; 
    
  }
  
  public static SetConstant mk(List<EnumerationElement> enumerations, SourceLocation location) {
    return new SetConstant(enumerations, location);
  }

  // === Accessors ===

  public List<EnumerationElement> getEnumerations() { return enumerations; }

  // === Visitor ===
  public void accept(IVisitor visitor) {
    visitor.visitSetConstant(this, enumerations, getLocation());
  }

  // === Others ===
  @Override
  public SetConstant clone() {
    List<EnumerationElement> newEnumerations = enumerations;
    
    return SetConstant.mk(newEnumerations, getLocation());
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("SetConstant ast node: ");
    
    sb.append("enumerations = ");
    sb.append(enumerations);
    sb.append(", ");
    
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2,sb.length());
    }
    return sb.toString();
  }
}

