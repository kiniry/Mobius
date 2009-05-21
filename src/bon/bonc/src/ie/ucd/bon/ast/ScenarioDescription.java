
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;

public class ScenarioDescription extends DynamicComponent {



  private final String name;
  private final List<LabelledAction> actions;
  private final String comment;


  // === Constructors and Factories ===
  protected ScenarioDescription(String name, List<LabelledAction> actions, String comment, SourceLocation location) {
    super(location);
    this.name = name; assert name != null;
    this.actions = actions; assert actions != null;
    this.comment = comment; 
    
  }
  
  public static ScenarioDescription mk(String name, List<LabelledAction> actions, String comment, SourceLocation location) {
    return new ScenarioDescription(name, actions, comment, location);
  }

  // === Accessors ===

  public String getName() { return name; }
  public List<LabelledAction> getActions() { return actions; }
  public String getComment() { return comment; }

  // === Others ===
  @Override
  public ScenarioDescription clone() {
    String newName = name;
    List<LabelledAction> newActions = actions;
    String newComment = comment;
    
    return ScenarioDescription.mk(newName, newActions, newComment, getLocation());
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("ScenarioDescription ast node: ");
    
    sb.append("name = ");
    sb.append(name);
    sb.append(", ");
    
    sb.append("actions = ");
    sb.append(actions);
    sb.append(", ");
    
    sb.append("comment = ");
    sb.append(comment);
    sb.append(", ");
    
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2,sb.length());
    }
    return sb.toString();
  }
}

