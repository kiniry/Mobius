
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;

public class KeywordConstant extends Constant {
  public static enum Constant {
    VOID, 
    CURRENT
  }


  private final Constant constant;


  // === Constructors and Factories ===
  protected KeywordConstant(Constant constant, SourceLocation location) {
    super(location);
    this.constant = constant; 
    
  }
  
  public static KeywordConstant mk(Constant constant, SourceLocation location) {
    return new KeywordConstant(constant, location);
  }

  // === Accessors ===

  public Constant getConstant() { return constant; }

  // === Visitor ===
  public void accept(IVisitor visitor) {
    visitor.visitKeywordConstant(this);
  }

  // === Others ===
  @Override
  public KeywordConstant clone() {
    Constant newConstant = constant;
    
    return KeywordConstant.mk(newConstant, getLocation());
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("KeywordConstant ast node: ");
    
    sb.append("constant = ");
    sb.append(constant);
    sb.append(", ");
    
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2,sb.length());
    }
    return sb.toString();
  }
}

