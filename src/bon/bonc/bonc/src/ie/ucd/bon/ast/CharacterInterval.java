
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;

public class CharacterInterval extends Interval {



  public final Character start;
  public final Character stop;


  // === Constructors and Factories ===
  protected CharacterInterval(Character start, Character stop, SourceLocation location) {
    super(location);
    this.start = start; assert start != null;
    this.stop = stop; assert stop != null;
    
  }
  
  public static CharacterInterval mk(Character start, Character stop, SourceLocation location) {
    return new CharacterInterval(start, stop, location);
  }

  // === Accessors ===

  public Character getStart() { return start; }
  public Character getStop() { return stop; }

  // === Visitor ===
  public void accept(IVisitorWithAdditions visitor) {
    visitor.visitCharacterInterval(this, start, stop, getLocation());
  }

  // === Others ===
  @Override
  public CharacterInterval clone() {
    Character newStart = start;
    Character newStop = stop;
    
    return CharacterInterval.mk(newStart, newStop, getLocation());
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("CharacterInterval ast node: ");
    
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

