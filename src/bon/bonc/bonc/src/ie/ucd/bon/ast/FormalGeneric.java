
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;

public class FormalGeneric extends AstNode {


  public final Type type;

  public final String identifier;


  // === Constructors and Factories ===
  protected FormalGeneric(String identifier, Type type, SourceLocation location) {
    super(location);
    this.identifier = identifier; assert identifier != null;
    this.type = type; 
  }
  
  public static FormalGeneric mk(String identifier, Type type, SourceLocation location) {
    return new FormalGeneric(identifier, type, location);
  }

  // === Accessors ===

  public String getIdentifier() { return identifier; }
  public Type getType() { return type; }

  // === Visitor ===
  public void accept(IVisitorWithAdditions visitor) {
    visitor.visitFormalGeneric(this, identifier, type, getLocation());
  }

  // === Others ===
  @Override
  public FormalGeneric clone() {
    String newIdentifier = identifier;
    Type newType = type == null ? null : type.clone();
    return FormalGeneric.mk(newIdentifier, newType, getLocation());
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("FormalGeneric ast node: ");
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

