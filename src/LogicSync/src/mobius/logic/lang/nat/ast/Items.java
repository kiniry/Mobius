
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package mobius.logic.lang.nat.ast;
import java.util.*;

import mobius.logic.lang.ast.FileLocation;

/** @author rgrig */
public class Items extends mobius.logic.lang.nat.ast.NLAst {


  private Items tail;

  private String id;
  private String description;



  // === Constructors and Factories ===
  protected Items() {}
  private Items(String id, String description, Items tail) {
    this.location = FileLocation.unknown();
    this.id = id; assert id != null;
    this.description = description; assert description != null;
    this.tail = tail; 
  }

  private Items(String id, String description, Items tail, FileLocation location) {
    this(id,description,tail);
    assert location != null;
    this.location = location;
  }
  
  public static Items mk(String id, String description, Items tail) {
    return new Items(id, description, tail);
  }

  public static Items mk(String id, String description, Items tail, FileLocation location) {
    return new Items(id, description, tail, location);
  }

  // === Accessors ===

  public String getId() { return id; }
  public String getDescription() { return description; }
  public Items getTail() { return tail; }

  public void setId(String id) { this.id = id; }
  public void setDescription(String description) { this.description = description; }
  public void setTail(Items tail) { this.tail = tail; }

  // === The Visitor pattern ===
  @Override
  public <R> R eval(Evaluator<R> evaluator) { 
    return evaluator.eval(this, id,description,tail); 
  }

  // === Others ===
  @Override
  public Items clone() {
    
      
        String newId = id;
      
    
      
        String newDescription = description;
      
    
      
        Items newTail = tail == null? 
          null : tail.clone();
      
    
    return Items.mk(newId, newDescription, newTail, location);
  }
}

