
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.ast.AstNode;

public class Clazz extends StaticComponent {


  private final ClassInterface classInterface;

  private final Boolean root;
  private final Boolean deferred;
  private final Boolean effective;
  private final Boolean reused;
  private final Boolean persistent;
  private final Boolean interfaced;
  private final List<FormalGeneric> generics;
  private final String comment;

private final SourceLocation location;

  // === Constructors and Factories ===
  protected Clazz(Boolean root, Boolean deferred, Boolean effective, Boolean reused, Boolean persistent, Boolean interfaced, ClassInterface classInterface, List<FormalGeneric> generics, String comment) {
    this(root,deferred,effective,reused,persistent,interfaced,classInterface,generics,comment, null);    
  }

  protected Clazz(Boolean root, Boolean deferred, Boolean effective, Boolean reused, Boolean persistent, Boolean interfaced, ClassInterface classInterface, List<FormalGeneric> generics, String comment, SourceLocation location) {
    
    assert location != null;
    this.location = location;
    this.root = root; assert root != null;
    this.deferred = deferred; assert deferred != null;
    this.effective = effective; assert effective != null;
    this.reused = reused; assert reused != null;
    this.persistent = persistent; assert persistent != null;
    this.interfaced = interfaced; assert interfaced != null;
    this.classInterface = classInterface; 
    this.generics = generics; 
    this.comment = comment; 
    
  }
  
  public static Clazz mk(Boolean root, Boolean deferred, Boolean effective, Boolean reused, Boolean persistent, Boolean interfaced, ClassInterface classInterface, List<FormalGeneric> generics, String comment) {
    return new Clazz(root, deferred, effective, reused, persistent, interfaced, classInterface, generics, comment);
  }

  public static Clazz mk(Boolean root, Boolean deferred, Boolean effective, Boolean reused, Boolean persistent, Boolean interfaced, ClassInterface classInterface, List<FormalGeneric> generics, String comment, SourceLocation location) {
    return new Clazz(root, deferred, effective, reused, persistent, interfaced, classInterface, generics, comment, location);
  }

  // === Accessors ===

  public Boolean getRoot() { return root; }
  public Boolean getDeferred() { return deferred; }
  public Boolean getEffective() { return effective; }
  public Boolean getReused() { return reused; }
  public Boolean getPersistent() { return persistent; }
  public Boolean getInterfaced() { return interfaced; }
  public ClassInterface getClassInterface() { return classInterface; }
  public List<FormalGeneric> getGenerics() { return generics; }
  public String getComment() { return comment; }

  // === Others ===
  @Override
  public Clazz clone() {
    Boolean newRoot = root;
    Boolean newDeferred = deferred;
    Boolean newEffective = effective;
    Boolean newReused = reused;
    Boolean newPersistent = persistent;
    Boolean newInterfaced = interfaced;
    ClassInterface newClassInterface = classInterface == null ? null : classInterface.clone();
    List<FormalGeneric> newGenerics = generics;
    String newComment = comment;
    
    return Clazz.mk(newRoot, newDeferred, newEffective, newReused, newPersistent, newInterfaced, newClassInterface, newGenerics, newComment, location);
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("Clazz ast node: ");
    
    sb.append("root = ");
    sb.append(root);
    sb.append(", ");
    
    sb.append("deferred = ");
    sb.append(deferred);
    sb.append(", ");
    
    sb.append("effective = ");
    sb.append(effective);
    sb.append(", ");
    
    sb.append("reused = ");
    sb.append(reused);
    sb.append(", ");
    
    sb.append("persistent = ");
    sb.append(persistent);
    sb.append(", ");
    
    sb.append("interfaced = ");
    sb.append(interfaced);
    sb.append(", ");
    
    sb.append("classInterface = ");
    sb.append(classInterface);
    sb.append(", ");
    
    sb.append("generics = ");
    sb.append(generics);
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

