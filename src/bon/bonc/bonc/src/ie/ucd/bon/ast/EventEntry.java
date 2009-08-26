
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;

public class EventEntry extends AstNode {



  private final String name;
  private final List<String> involved;


  // === Constructors and Factories ===
  protected EventEntry(String name, List<String> involved, SourceLocation location) {
    super(location);
    this.name = name; assert name != null;
    this.involved = involved; assert involved != null;
    
  }
  
  public static EventEntry mk(String name, List<String> involved, SourceLocation location) {
    return new EventEntry(name, involved, location);
  }

  // === Accessors ===

  public String getName() { return name; }
  public List<String> getInvolved() { return involved; }

  // === Visitor ===
  public void accept(IVisitorWithAdditions visitor) {
    visitor.visitEventEntry(this, name, involved, getLocation());
  }

  // === Others ===
  @Override
  public EventEntry clone() {
    String newName = name;
    List<String> newInvolved = involved;
    
    return EventEntry.mk(newName, newInvolved, getLocation());
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("EventEntry ast node: ");
    
    sb.append("name = ");
    sb.append(name);
    sb.append(", ");
    
    sb.append("involved = ");
    sb.append(involved);
    sb.append(", ");
    
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2,sb.length());
    }
    return sb.toString();
  }
}

