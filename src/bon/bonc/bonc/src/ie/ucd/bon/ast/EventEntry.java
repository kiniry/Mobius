
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;

public class EventEntry extends AstNode {



  public final String description;
  public final List<String> involved;


  // === Constructors and Factories ===
  protected EventEntry(String description, List<String> involved, SourceLocation location) {
    super(location);
    this.description = description; assert description != null;
    this.involved = involved; assert involved != null;
  }
  
  public static EventEntry mk(String description, List<String> involved, SourceLocation location) {
    return new EventEntry(description, involved, location);
  }

  // === Accessors ===

  public String getDescription() { return description; }
  public List<String> getInvolved() { return involved; }

  // === Visitor ===
  public void accept(IVisitorWithAdditions visitor) {
    visitor.visitEventEntry(this, description, involved, getLocation());
  }

  // === Others ===
  @Override
  public EventEntry clone() {
    String newDescription = description;
    List<String> newInvolved = involved;
    return EventEntry.mk(newDescription, newInvolved, getLocation());
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("EventEntry ast node: ");
    sb.append("description = ");
    sb.append(description);
    sb.append(", ");
        sb.append("involved = ");
    sb.append(involved);
    sb.append(", ");
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2, sb.length());
    }
    return sb.toString();
  }
}

