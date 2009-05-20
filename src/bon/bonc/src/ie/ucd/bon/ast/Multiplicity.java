
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.ast.AstNode;

public class Multiplicity extends ClientEntityExpression {



  private final Integer multiplicity;

  private final SourceLocation location;

  // === Constructors and Factories ===
  protected Multiplicity(Integer multiplicity) {
    this(multiplicity, null);    
  }

  protected Multiplicity(Integer multiplicity, SourceLocation location) {
    
    assert location != null;
    this.location = location;
    this.multiplicity = multiplicity; assert multiplicity != null;
    
  }
  
  public static Multiplicity mk(Integer multiplicity) {
    return new Multiplicity(multiplicity);
  }

  public static Multiplicity mk(Integer multiplicity, SourceLocation location) {
    return new Multiplicity(multiplicity, location);
  }
  
  public SourceLocation getLocation() {
    return location;
  }

  // === Accessors ===

  public Integer getMultiplicity() { return multiplicity; }

  // === Others ===
  @Override
  public Multiplicity clone() {
    Integer newMultiplicity = multiplicity;
    
    return Multiplicity.mk(newMultiplicity, location);
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

