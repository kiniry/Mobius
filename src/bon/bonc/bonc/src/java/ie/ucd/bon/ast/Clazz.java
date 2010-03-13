
/**
 * Copyright (c) 2007-2010, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 *
 * This class is generated automatically from normal_classes.tpl.
 * Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.util.StringUtil;

public class Clazz extends StaticComponent {
  public static enum Mod {
    NONE, 
    DEFERRED, 
    ROOT, 
    EFFECTIVE
  }

  public final ClassName name;
  public final ClassInterface classInterface;

  public final List<FormalGeneric> generics;
  public final Mod mod;
  public final Boolean reused;
  public final Boolean persistent;
  public final Boolean interfaced;
  public final String comment;


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
    return StringUtil.prettyPrint(this);
  }
}

