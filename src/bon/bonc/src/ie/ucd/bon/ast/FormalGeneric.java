
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.ast.AstNode;

public class FormalGeneric extends AstNode {



  private final String identifier;
  private final BONType type;

private final SourceLocation location;

  // === Constructors and Factories ===
  protected FormalGeneric(String identifier, BONType type) {
    this(identifier,type, null);    
  }

  protected FormalGeneric(String identifier, BONType type, SourceLocation location) {
    
    assert location != null;
    this.location = location;
    this.identifier = identifier; assert identifier != null;
    this.type = type; 
    
  }
  
  public static FormalGeneric mk(String identifier, BONType type) {
    return new FormalGeneric(identifier, type);
  }

  public static FormalGeneric mk(String identifier, BONType type, SourceLocation location) {
    return new FormalGeneric(identifier, type, location);
  }

  // === Accessors ===

  public String getIdentifier() { return identifier; }
  public BONType getType() { return type; }

  // === Others ===
  @Override
  public FormalGeneric clone() {
    String newIdentifier = identifier;
    BONType newType = type;
    
    return FormalGeneric.mk(newIdentifier, newType, location);
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
      sb.delete(sb.length()-2,sb.length());
    }
    return sb.toString();
  }
}

