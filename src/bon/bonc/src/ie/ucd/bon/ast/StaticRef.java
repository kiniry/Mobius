
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.ast.AstNode;

public class StaticRef extends AstNode {



  private final BONType type;

  private final SourceLocation location;

  // === Constructors and Factories ===
  protected StaticRef(BONType type) {
    this(type, null);    
  }

  protected StaticRef(BONType type, SourceLocation location) {
    
    assert location != null;
    this.location = location;
    this.type = type; assert type != null;
    
  }
  
  public static StaticRef mk(BONType type) {
    return new StaticRef(type);
  }

  public static StaticRef mk(BONType type, SourceLocation location) {
    return new StaticRef(type, location);
  }

  // === Accessors ===

  public BONType getType() { return type; }

  // === Others ===
  @Override
  public StaticRef clone() {
    BONType newType = type;
    
    return StaticRef.mk(newType, location);
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("StaticRef ast node: ");
    
    sb.append("type = ");
    sb.append(type);
    sb.append(", ");
    
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2,sb.length());
    }
    return sb.toString();
  }
}

