
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

public class ObjectGroup extends DynamicComponent {
  public static enum Nameless {
    NOTNAMELESS, 
    NAMELESS
  }


  public final Nameless nameless;
  public final String name;
  public final List<DynamicComponent> components;
  public final String comment;


  // === Constructors and Factories ===
  protected ObjectGroup(Nameless nameless, String name, List<DynamicComponent> components, String comment, SourceLocation location) {
    super(location);
    this.nameless = nameless; 
    this.name = name; assert name != null;
    this.components = components; assert components != null;
    this.comment = comment; 
  }

  public static ObjectGroup mk(Nameless nameless, String name, List<DynamicComponent> components, String comment, SourceLocation location) {
    return new ObjectGroup(nameless, name, components, comment, location);
  }

  // === Accessors ===

  public Nameless getNameless() { return nameless; }
  public String getName() { return name; }
  public List<DynamicComponent> getComponents() { return components; }
  public String getComment() { return comment; }

  // === Visitor ===
  public void accept(IVisitorWithAdditions visitor) {
    visitor.visitObjectGroup(this, nameless, name, components, comment, getLocation());
  }

  // === Others ===
  @Override
  public ObjectGroup clone() {
    Nameless newNameless = nameless;
    String newName = name;
    List<DynamicComponent> newComponents = components;
    String newComment = comment;
    return ObjectGroup.mk(newNameless, newName, newComponents, newComment, getLocation());
  }

  @Override
  public String toString() {
    return StringUtil.prettyPrint(this);
  }
}

