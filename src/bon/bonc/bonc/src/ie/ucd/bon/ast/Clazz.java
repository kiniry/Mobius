
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;

public class Clazz extends StaticComponent {
  public static enum Mod {
    NONE, 
    DEFERRED, 
    ROOT, 
    EFFECTIVE
  }

  private final ClassName name;
  private final ClassInterface classInterface;

  private final List<FormalGeneric> generics;
  private final Mod mod;
  private final Boolean reused;
  private final Boolean persistent;
  private final Boolean interfaced;
  private final String comment;


  // === Constructors and Factories ===
  protected Clazz(ClassName name, List<FormalGeneric> generics, Mod mod, ClassInterface classInterface, Boolean reused, Boolean persistent, Boolean interfaced, String comment, SourceLocation location) {
    super(location);
    this.name = name; assert name != null;
    this.generics = generics; 
    this.mod = mod; 
    this.classInterface = classInterface; 
    this.reused = reused; assert reused != null;
    this.persistent = persistent; assert persistent != null;
    this.interfaced = interfaced; assert interfaced != null;
    this.comment = comment; 
    
  }
  
  public static Clazz mk(ClassName name, List<FormalGeneric> generics, Mod mod, ClassInterface classInterface, Boolean reused, Boolean persistent, Boolean interfaced, String comment, SourceLocation location) {
    return new Clazz(name, generics, mod, classInterface, reused, persistent, interfaced, comment, location);
  }

  // === Accessors ===

  public ClassName getName() { return name; }
  public List<FormalGeneric> getGenerics() { return generics; }
  public Mod getMod() { return mod; }
  public ClassInterface getClassInterface() { return classInterface; }
  public Boolean getReused() { return reused; }
  public Boolean getPersistent() { return persistent; }
  public Boolean getInterfaced() { return interfaced; }
  public String getComment() { return comment; }

  // === Visitor ===
  public void accept(IVisitorWithAdditions visitor) {
    visitor.visitClazz(this, name, generics, mod, classInterface, reused, persistent, interfaced, comment, getLocation());
  }

  // === Others ===
  @Override
  public Clazz clone() {
    ClassName newName = name == null ? null : name.clone();
    List<FormalGeneric> newGenerics = generics;
    Mod newMod = mod;
    ClassInterface newClassInterface = classInterface == null ? null : classInterface.clone();
    Boolean newReused = reused;
    Boolean newPersistent = persistent;
    Boolean newInterfaced = interfaced;
    String newComment = comment;
    
    return Clazz.mk(newName, newGenerics, newMod, newClassInterface, newReused, newPersistent, newInterfaced, newComment, getLocation());
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("Clazz ast node: ");
    
    sb.append("name = ");
    sb.append(name);
    sb.append(", ");
    
    sb.append("generics = ");
    sb.append(generics);
    sb.append(", ");
    
    sb.append("mod = ");
    sb.append(mod);
    sb.append(", ");
    
    sb.append("classInterface = ");
    sb.append(classInterface);
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
    
    sb.append("comment = ");
    sb.append(comment);
    sb.append(", ");
    
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2,sb.length());
    }
    return sb.toString();
  }
}

