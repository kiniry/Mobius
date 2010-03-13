
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

public class ClassEntry extends AstNode {



  public final String name;
  public final String description;


  // === Constructors and Factories ===
  protected ClassEntry(String name, String description, SourceLocation location) {
    super(location);
    this.name = name; assert name != null;
    this.description = description; assert description != null;
  }

  public static ClassEntry mk(String name, String description, SourceLocation location) {
    return new ClassEntry(name, description, location);
  }

  // === Accessors ===

  public String getName() { return name; }
  public String getDescription() { return description; }

  // === Visitor ===
  public void accept(IVisitorWithAdditions visitor) {
    visitor.visitClassEntry(this, name, description, getLocation());
  }

  // === Others ===
  @Override
  public ClassEntry clone() {
    String newName = name;
    String newDescription = description;
    return ClassEntry.mk(newName, newDescription, getLocation());
  }

  @Override
  public String toString() {
    return StringUtil.prettyPrint(this);
  }
}

