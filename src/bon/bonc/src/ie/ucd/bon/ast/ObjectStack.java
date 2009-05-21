
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.ast.AstNode;

public class ObjectStack extends DynamicComponent {


  private final ObjectName name;

  private final String comment;

  private final SourceLocation location;

  // === Constructors and Factories ===
  protected ObjectStack(ObjectName name, String comment) {
    this(name,comment, null);    
  }

  protected ObjectStack(ObjectName name, String comment, SourceLocation location) {
    
    assert location != null;
    this.location = location;
    this.name = name; assert name != null;
    this.comment = comment; 
    
  }
  
  public static ObjectStack mk(ObjectName name, String comment) {
    return new ObjectStack(name, comment);
  }

  public static ObjectStack mk(ObjectName name, String comment, SourceLocation location) {
    return new ObjectStack(name, comment, location);
  }
  
  public SourceLocation getLocation() {
    return location;
  }

  // === Accessors ===

  public ObjectName getName() { return name; }
  public String getComment() { return comment; }

  // === Others ===
  @Override
  public ObjectStack clone() {
    ObjectName newName = name == null ? null : name.clone();
    String newComment = comment;
    
    return ObjectStack.mk(newName, newComment, location);
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("ObjectStack ast node: ");
    
    sb.append("name = ");
    sb.append(name);
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

