
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.ast.AstNode;

public class TypeRange extends VariableRange {



  private final List<String> identifiers;
  private final BONType type;

private final SourceLocation location;

  // === Constructors and Factories ===
  protected TypeRange(List<String> identifiers, BONType type) {
    this(identifiers,type, null);    
  }

  protected TypeRange(List<String> identifiers, BONType type, SourceLocation location) {
    
    assert location != null;
    this.location = location;
    this.identifiers = identifiers; assert identifiers != null;
    this.type = type; assert type != null;
    
  }
  
  public static TypeRange mk(List<String> identifiers, BONType type) {
    return new TypeRange(identifiers, type);
  }

  public static TypeRange mk(List<String> identifiers, BONType type, SourceLocation location) {
    return new TypeRange(identifiers, type, location);
  }

  // === Accessors ===

  public List<String> getIdentifiers() { return identifiers; }
  public BONType getType() { return type; }

  // === Others ===
  @Override
  public TypeRange clone() {
    List<String> newIdentifiers = identifiers;
    BONType newType = type;
    
    return TypeRange.mk(newIdentifiers, newType, location);
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("TypeRange ast node: ");
    
    sb.append("identifiers = ");
    sb.append(identifiers);
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

