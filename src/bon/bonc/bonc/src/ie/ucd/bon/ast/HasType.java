
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;

public class HasType extends AstNode {


  public final TypeMark mark;
  public final Type type;



  // === Constructors and Factories ===
  protected HasType(TypeMark mark, Type type, SourceLocation location) {
    super(location);
    this.mark = mark; assert mark != null;
    this.type = type; assert type != null;
    
  }
  
  public static HasType mk(TypeMark mark, Type type, SourceLocation location) {
    return new HasType(mark, type, location);
  }

  // === Accessors ===

  public TypeMark getMark() { return mark; }
  public Type getType() { return type; }

  // === Visitor ===
  public void accept(IVisitorWithAdditions visitor) {
    visitor.visitHasType(this, mark, type, getLocation());
  }

  // === Others ===
  @Override
  public HasType clone() {
    TypeMark newMark = mark == null ? null : mark.clone();
    Type newType = type == null ? null : type.clone();
    
    return HasType.mk(newMark, newType, getLocation());
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

