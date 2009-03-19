
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package mobius.logic.lang.nat.ast;
import java.util.*;

import mobius.logic.lang.ast.FileLocation;

/** @author rgrig */
public class Logics extends mobius.logic.lang.nat.ast.NLAst {


  private Logic logic;
  private Logics tail;




  // === Constructors and Factories ===
  protected Logics() {}
  private Logics(Logic logic, Logics tail) {
    this.location = FileLocation.unknown();
    this.logic = logic; assert logic != null;
    this.tail = tail; 
  }

  private Logics(Logic logic, Logics tail, FileLocation location) {
    this(logic,tail);
    assert location != null;
    this.location = location;
  }
  
  public static Logics mk(Logic logic, Logics tail) {
    return new Logics(logic, tail);
  }

  public static Logics mk(Logic logic, Logics tail, FileLocation location) {
    return new Logics(logic, tail, location);
  }

  // === Accessors ===

  public Logic getLogic() { return logic; }
  public Logics getTail() { return tail; }

  public void setLogic(Logic logic) { this.logic = logic; }
  public void setTail(Logics tail) { this.tail = tail; }

  // === The Visitor pattern ===
  @Override
  public <R> R eval(Evaluator<R> evaluator) { 
    return evaluator.eval(this, logic,tail); 
  }

  // === Others ===
  @Override
  public Logics clone() {
    
      
        Logic newLogic = logic == null? 
          null : logic.clone();
      
    
      
        Logics newTail = tail == null? 
          null : tail.clone();
      
    
    return Logics.mk(newLogic, newTail, location);
  }
}

