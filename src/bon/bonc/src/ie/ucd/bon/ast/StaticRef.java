
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;

public class StaticRef extends AstNode {


  private final StaticRefPart name;

  private final List<StaticRefPart> prefix;


  // === Constructors and Factories ===
  protected StaticRef(List<StaticRefPart> prefix, StaticRefPart name, SourceLocation location) {
    super(location);
    this.prefix = prefix; assert prefix != null;
    this.name = name; assert name != null;
    
  }
  
  public static StaticRef mk(List<StaticRefPart> prefix, StaticRefPart name, SourceLocation location) {
    return new StaticRef(prefix, name, location);
  }

  // === Accessors ===

  public List<StaticRefPart> getPrefix() { return prefix; }
  public StaticRefPart getName() { return name; }

  // === Visitor ===
  public void accept(IVisitor visitor) {
    visitor.visitStaticRef(this, prefix, name, getLocation());
  }

  // === Others ===
  @Override
  public StaticRef clone() {
    List<StaticRefPart> newPrefix = prefix;
    StaticRefPart newName = name == null ? null : name.clone();
    
    return StaticRef.mk(newPrefix, newName, getLocation());
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("StaticRef ast node: ");
    
    sb.append("prefix = ");
    sb.append(prefix);
    sb.append(", ");
    
    sb.append("name = ");
    sb.append(name);
    sb.append(", ");
    
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2,sb.length());
    }
    return sb.toString();
  }
}

