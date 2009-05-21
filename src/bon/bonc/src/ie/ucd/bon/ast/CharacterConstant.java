
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;

public class CharacterConstant extends ManifestConstant {



  private final Character value;


  // === Constructors and Factories ===
  protected CharacterConstant(Character value, SourceLocation location) {
    super(location);
    this.value = value; assert value != null;
    
  }
  
  public static CharacterConstant mk(Character value, SourceLocation location) {
    return new CharacterConstant(value, location);
  }

  // === Accessors ===

  public Character getValue() { return value; }

  // === Others ===
  @Override
  public CharacterConstant clone() {
    Character newValue = value;
    
    return CharacterConstant.mk(newValue, getLocation());
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("CharacterConstant ast node: ");
    
    sb.append("value = ");
    sb.append(value);
    sb.append(", ");
    
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2,sb.length());
    }
    return sb.toString();
  }
}

