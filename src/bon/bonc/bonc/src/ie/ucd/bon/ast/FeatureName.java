
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;

public class FeatureName extends IndirectionFeaturePart {



  public final String name;


  // === Constructors and Factories ===
  protected FeatureName(String name, SourceLocation location) {
    super(location);
    this.name = name; assert name != null;
  }
  
  public static FeatureName mk(String name, SourceLocation location) {
    return new FeatureName(name, location);
  }

  // === Accessors ===

  public String getName() { return name; }

  // === Visitor ===
  public void accept(IVisitorWithAdditions visitor) {
    visitor.visitFeatureName(this, name, getLocation());
  }

  // === Others ===
  @Override
  public FeatureName clone() {
    String newName = name;
    return FeatureName.mk(newName, getLocation());
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("FeatureName ast node: ");
    sb.append("name = ");
    sb.append(name);
    sb.append(", ");
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2, sb.length());
    }
    return sb.toString();
  }
}

