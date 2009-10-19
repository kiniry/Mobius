
/**
  This class is generated automatically from normal_classes.tpl.
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;

public class RealConstant extends ManifestConstant {



  public final Double value;


  // === Constructors and Factories ===
  protected RealConstant(Double value, SourceLocation location) {
    super(location);
    this.value = value; assert value != null;
  }

  public static RealConstant mk(Double value, SourceLocation location) {
    return new RealConstant(value, location);
  }

  // === Accessors ===

  public Double getValue() { return value; }

  // === Visitor ===
  public void accept(IVisitorWithAdditions visitor) {
    visitor.visitRealConstant(this, value, getLocation());
  }

  // === Others ===
  @Override
  public RealConstant clone() {
    Double newValue = value;
    return RealConstant.mk(newValue, getLocation());
  }

  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("RealConstant ast node: ");
    sb.append("value = ");
    sb.append(value);
    sb.append(", ");
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2, sb.length());
    }
    return sb.toString();
  }
}

