
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.ast.AstNode;

public class HasType extends AstNode {


  private final TypeMark mark;

  private final BONType type;

private final SourceLocation location;

  // === Constructors and Factories ===
  protected HasType(TypeMark mark, BONType type) {
    this(mark,type, null);    
  }

  protected HasType(TypeMark mark, BONType type, SourceLocation location) {
    
    assert location != null;
    this.location = location;
    this.mark = mark; assert mark != null;
    this.type = type; assert type != null;
    
  }
  
  public static HasType mk(TypeMark mark, BONType type) {
    return new HasType(mark, type);
  }

  public static HasType mk(TypeMark mark, BONType type, SourceLocation location) {
    return new HasType(mark, type, location);
  }

  // === Accessors ===

  public TypeMark getMark() { return mark; }
  public BONType getType() { return type; }

  // === Others ===
  @Override
  public HasType clone() {
    TypeMark newMark = mark == null ? null : mark.clone();
    BONType newType = type;
    
    return HasType.mk(newMark, newType, location);
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("HasType ast node: ");
    
    sb.append("mark = ");
    sb.append(mark);
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

