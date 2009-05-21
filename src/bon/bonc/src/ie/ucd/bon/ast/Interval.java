
/**
  This class is generated automatically from abstract_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import ie.ucd.bon.source.SourceLocation;

public abstract class Interval extends EnumerationElement {

  public Interval(SourceLocation location) {
    super(location);
  }

  // a more specific return type
  @Override
  public abstract Interval clone();
}
