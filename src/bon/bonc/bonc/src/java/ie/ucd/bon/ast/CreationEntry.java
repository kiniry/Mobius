
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

public class CreationEntry extends AstNode {


  public final ClassName name;

  public final List<String> types;


  // === Constructors and Factories ===
  protected CreationEntry(ClassName name, List<String> types, SourceLocation location) {
    super(location);
    this.name = name; assert name != null;
    this.types = types; assert types != null;
  }

  public static CreationEntry mk(ClassName name, List<String> types, SourceLocation location) {
    return new CreationEntry(name, types, location);
  }

  // === Accessors ===

  public ClassName getName() { return name; }
  public List<String> getTypes() { return types; }

  // === Visitor ===
  public void accept(IVisitorWithAdditions visitor) {
    visitor.visitCreationEntry(this, name, types, getLocation());
  }

  // === Others ===
  @Override
  public CreationEntry clone() {
    ClassName newName = name == null ? null : name.clone();
    List<String> newTypes = types;
    return CreationEntry.mk(newName, newTypes, getLocation());
  }

  @Override
  public String toString() {
    return StringUtil.prettyPrint(this);
  }
}

