
/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 *
 * This class is generated automatically from normal_classes.tpl.
 * Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;

public class TypeMark extends AstNode {
  public static enum Mark {
    HASTYPE, 
    NONE, 
    SHAREDMARK, 
    AGGREGATE
  }


  public final Mark mark;
  public final Integer multiplicity;


  // === Constructors and Factories ===
  protected TypeMark(Mark mark, Integer multiplicity, SourceLocation location) {
    super(location);
    this.mark = mark; 
    this.multiplicity = multiplicity; 
  }

  public static TypeMark mk(Mark mark, Integer multiplicity, SourceLocation location) {
    return new TypeMark(mark, multiplicity, location);
  }

  // === Accessors ===

  public Mark getMark() { return mark; }
  public Integer getMultiplicity() { return multiplicity; }

  // === Visitor ===
  public void accept(IVisitorWithAdditions visitor) {
    visitor.visitTypeMark(this, mark, multiplicity, getLocation());
  }

  // === Others ===
  @Override
  public TypeMark clone() {
    Mark newMark = mark;
    Integer newMultiplicity = multiplicity;
    return TypeMark.mk(newMark, newMultiplicity, getLocation());
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
      sb.delete(sb.length()-2, sb.length());
    }
    return sb.toString();
  }
}

