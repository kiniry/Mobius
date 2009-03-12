/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker;

public class TypeMark {

  public static final TypeMark NONE = new TypeMark("");
  public static final TypeMark STANDARD = new TypeMark(":");
  public static final TypeMark AGGREGATE = new TypeMark(":{");
  
  private final String markString;
  
  private final boolean hasMark;
  private final boolean isAggregate;
  private final boolean isSharedMark;
  
  private final int multiplicity;
  private static final int NO_MULTIPLICITY = Integer.MIN_VALUE;
  
  private TypeMark(String mark) {
    this.markString = mark;
    if ("".equals(mark)) {
      hasMark = false;
      isAggregate = false;
      isSharedMark = false;
      multiplicity = NO_MULTIPLICITY;
    } else if (":".equals(mark)) {
      hasMark = true;
      isAggregate = false;
      isSharedMark = false;
      multiplicity = NO_MULTIPLICITY;
    } else if (":{".equals(mark)) {
      hasMark = true;
      isAggregate = true;
      isSharedMark = false;
      multiplicity = NO_MULTIPLICITY;
    } else {
      //First char should be ':'
      mark = mark.substring(1).trim();
      hasMark = true;
      isAggregate = false;
      isSharedMark = true;
      multiplicity = Integer.parseInt(mark);
    }
  }
  
  public static TypeMark make(String s) {
    s = s.trim();
    if ("".equals(s)) {
      return NONE;
    } else if (":".equals(s)) {
      return STANDARD;
    } else if (":{".equals(s)) {
      return AGGREGATE;
    } else {
      return new TypeMark(s);
    }
  }

  @Override
  public String toString() {
    return markString;
  }

  public boolean hasMark() {
    return hasMark;
  }

  public boolean isAggregate() {
    return isAggregate;
  }

  public boolean isSharedMark() {
    return isSharedMark;
  }

  public int getMultiplicity() {
    return multiplicity;
  }
  
}
