
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.ast.AstNode;

public class Clazz extends StaticComponent {
  public static enum ModA {
    NONE, 
    DEFERRED, 
    ROOT, 
    EFFECTIVE
  }  public static enum ModB {
    INTERFACED, 
    REUSED, 
    PERSISTENT, 
    NONE
  }

  private final ClassInterface classInterface;

  private final ModA modA;
  private final ModB modB;
  private final List<FormalGeneric> generics;
  private final String comment;

  private final SourceLocation location;

  // === Constructors and Factories ===
  protected Clazz(ModA modA, ModB modB, ClassInterface classInterface, List<FormalGeneric> generics, String comment) {
    this(modA,modB,classInterface,generics,comment, null);    
  }

  protected Clazz(ModA modA, ModB modB, ClassInterface classInterface, List<FormalGeneric> generics, String comment, SourceLocation location) {
    
    assert location != null;
    this.location = location;
    this.modA = modA; 
    this.modB = modB; 
    this.classInterface = classInterface; 
    this.generics = generics; 
    this.comment = comment; 
    
  }
  
  public static Clazz mk(ModA modA, ModB modB, ClassInterface classInterface, List<FormalGeneric> generics, String comment) {
    return new Clazz(modA, modB, classInterface, generics, comment);
  }

  public static Clazz mk(ModA modA, ModB modB, ClassInterface classInterface, List<FormalGeneric> generics, String comment, SourceLocation location) {
    return new Clazz(modA, modB, classInterface, generics, comment, location);
  }
  
  public SourceLocation getLocation() {
    return location;
  }

  // === Accessors ===

  public ModA getModA() { return modA; }
  public ModB getModB() { return modB; }
  public ClassInterface getClassInterface() { return classInterface; }
  public List<FormalGeneric> getGenerics() { return generics; }
  public String getComment() { return comment; }

  // === Others ===
  @Override
  public Clazz clone() {
    ModA newModA = modA;
    ModB newModB = modB;
    ClassInterface newClassInterface = classInterface == null ? null : classInterface.clone();
    List<FormalGeneric> newGenerics = generics;
    String newComment = comment;
    
    return Clazz.mk(newModA, newModB, newClassInterface, newGenerics, newComment, location);
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("Clazz ast node: ");
    
    sb.append("modA = ");
    sb.append(modA);
    sb.append(", ");
    
    sb.append("modB = ");
    sb.append(modB);
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

