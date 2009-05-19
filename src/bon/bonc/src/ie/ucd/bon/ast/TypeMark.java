
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.ast.AstNode;

public class TypeMark extends AstNode {



  private final Boolean hasMark;
  private final Boolean isAggregate;
  private final Boolean isSharedMark;
  private final Integer multiplicity;

private final SourceLocation location;

  // === Constructors and Factories ===
  protected TypeMark(Boolean hasMark, Boolean isAggregate, Boolean isSharedMark, Integer multiplicity) {
    this(hasMark,isAggregate,isSharedMark,multiplicity, null);    
  }

  protected TypeMark(Boolean hasMark, Boolean isAggregate, Boolean isSharedMark, Integer multiplicity, SourceLocation location) {
    
    assert location != null;
    this.location = location;
    this.hasMark = hasMark; assert hasMark != null;
    this.isAggregate = isAggregate; assert isAggregate != null;
    this.isSharedMark = isSharedMark; assert isSharedMark != null;
    this.multiplicity = multiplicity; assert multiplicity != null;
    
  }
  
  public static TypeMark mk(Boolean hasMark, Boolean isAggregate, Boolean isSharedMark, Integer multiplicity) {
    return new TypeMark(hasMark, isAggregate, isSharedMark, multiplicity);
  }

  public static TypeMark mk(Boolean hasMark, Boolean isAggregate, Boolean isSharedMark, Integer multiplicity, SourceLocation location) {
    return new TypeMark(hasMark, isAggregate, isSharedMark, multiplicity, location);
  }

  // === Accessors ===

  public Boolean getHasMark() { return hasMark; }
  public Boolean getIsAggregate() { return isAggregate; }
  public Boolean getIsSharedMark() { return isSharedMark; }
  public Integer getMultiplicity() { return multiplicity; }

  // === Others ===
  @Override
  public TypeMark clone() {
    Boolean newHasMark = hasMark;
    Boolean newIsAggregate = isAggregate;
    Boolean newIsSharedMark = isSharedMark;
    Integer newMultiplicity = multiplicity;
    
    return TypeMark.mk(newHasMark, newIsAggregate, newIsSharedMark, newMultiplicity, location);
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("TypeMark ast node: ");
    
    sb.append("hasMark = ");
    sb.append(hasMark);
    sb.append(", ");
    
    sb.append("isAggregate = ");
    sb.append(isAggregate);
    sb.append(", ");
    
    sb.append("isSharedMark = ");
    sb.append(isSharedMark);
    sb.append(", ");
    
    sb.append("multiplicity = ");
    sb.append(multiplicity);
    sb.append(", ");
    
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2,sb.length());
    }
    return sb.toString();
  }
}

