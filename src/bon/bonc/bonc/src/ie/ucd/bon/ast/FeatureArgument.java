
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;

public class FeatureArgument extends AstNode {


  public final Type type;

  public final String identifier;


  // === Constructors and Factories ===
  protected FeatureArgument(String identifier, Type type, SourceLocation location) {
    super(location);
    this.identifier = identifier; 
    this.type = type; assert type != null;
  }
  
  public static FeatureArgument mk(String identifier, Type type, SourceLocation location) {
    return new FeatureArgument(identifier, type, location);
  }

  // === Accessors ===

  public String getIdentifier() { return identifier; }
  public Type getType() { return type; }

  // === Visitor ===
  public void accept(IVisitorWithAdditions visitor) {
    visitor.visitFeatureArgument(this, identifier, type, getLocation());
  }

  // === Others ===
  @Override
  public FeatureArgument clone() {
    String newIdentifier = identifier;
    Type newType = type == null ? null : type.clone();
    return FeatureArgument.mk(newIdentifier, newType, getLocation());
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("FeatureArgument ast node: ");
    sb.append("identifier = ");
    sb.append(identifier);
    sb.append(", ");
        sb.append("type = ");
    sb.append(type);
    sb.append(", ");
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2, sb.length());
    }
    return sb.toString();
  }
}

