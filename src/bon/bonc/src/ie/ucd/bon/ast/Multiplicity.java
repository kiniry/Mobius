
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;

public class Multiplicity extends ClientEntityExpression {



  private final Integer multiplicity;


  // === Constructors and Factories ===
  protected Multiplicity(Integer multiplicity, SourceLocation location) {
    super(location);
    this.multiplicity = multiplicity; assert multiplicity != null;
    
  }
  
  public static Multiplicity mk(Integer multiplicity, SourceLocation location) {
    return new Multiplicity(multiplicity, location);
  }

  // === Accessors ===

  public Integer getMultiplicity() { return multiplicity; }

  // === Visitor ===
  public void accept(IVisitor visitor) {
    visitor.visitMultiplicity(this);
  }

  // === Others ===
  @Override
  public Multiplicity clone() {
    Integer newMultiplicity = multiplicity;
    
    return Multiplicity.mk(newMultiplicity, getLocation());
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("Multiplicity ast node: ");
    
    sb.append("multiplicity = ");
    sb.append(multiplicity);
    sb.append(", ");
    
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2,sb.length());
    }
    return sb.toString();
  }
}

