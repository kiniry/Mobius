
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;

public class IntegerInterval extends Interval {



  public final Integer start;
  public final Integer stop;


  // === Constructors and Factories ===
  protected IntegerInterval(Integer start, Integer stop, SourceLocation location) {
    super(location);
    this.start = start; assert start != null;
    this.stop = stop; assert stop != null;
    
  }
  
  public static IntegerInterval mk(Integer start, Integer stop, SourceLocation location) {
    return new IntegerInterval(start, stop, location);
  }

  // === Accessors ===

  public Integer getStart() { return start; }
  public Integer getStop() { return stop; }

  // === Visitor ===
  public void accept(IVisitorWithAdditions visitor) {
    visitor.visitIntegerInterval(this, start, stop, getLocation());
  }

  // === Others ===
  @Override
  public IntegerInterval clone() {
    Integer newStart = start;
    Integer newStop = stop;
    
    return IntegerInterval.mk(newStart, newStop, getLocation());
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("IntegerInterval ast node: ");
    
    sb.append("start = ");
    sb.append(start);
    sb.append(", ");
    
    sb.append("stop = ");
    sb.append(stop);
    sb.append(", ");
    
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2,sb.length());
    }
    return sb.toString();
  }
}

