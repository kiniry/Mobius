
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.ast.AstNode;

public class TypeMark extends AstNode {
  public static enum Mark {
    HASTYPE, 
    NONE, 
    SHAREDMARK, 
    AGGREGATE
  }


  private final Mark mark;
  private final Integer multiplicity;

  private final SourceLocation location;

  // === Constructors and Factories ===
  protected TypeMark(Mark mark, Integer multiplicity) {
    this(mark,multiplicity, null);    
  }

  protected TypeMark(Mark mark, Integer multiplicity, SourceLocation location) {
    
    assert location != null;
    this.location = location;
    this.mark = mark; 
    this.multiplicity = multiplicity; 
    
  }
  
  public static TypeMark mk(Mark mark, Integer multiplicity) {
    return new TypeMark(mark, multiplicity);
  }

  public static TypeMark mk(Mark mark, Integer multiplicity, SourceLocation location) {
    return new TypeMark(mark, multiplicity, location);
  }

  // === Accessors ===

  public Mark getMark() { return mark; }
  public Integer getMultiplicity() { return multiplicity; }

  // === Others ===
  @Override
  public TypeMark clone() {
    Mark newMark = mark;
    Integer newMultiplicity = multiplicity;
    
    return TypeMark.mk(newMark, newMultiplicity, location);
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("TypeMark ast node: ");
    
    sb.append("mark = ");
    sb.append(mark);
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

