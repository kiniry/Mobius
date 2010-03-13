
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

public class StaticRef extends AstNode {


  public final StaticRefPart name;

  public final List<StaticRefPart> prefix;


  // === Constructors and Factories ===
  protected StaticRef(List<StaticRefPart> prefix, StaticRefPart name, SourceLocation location) {
    super(location);
    this.prefix = prefix; assert prefix != null;
    this.name = name; assert name != null;
  }

  public static StaticRef mk(List<StaticRefPart> prefix, StaticRefPart name, SourceLocation location) {
    return new StaticRef(prefix, name, location);
  }

  // === Accessors ===

  public List<StaticRefPart> getPrefix() { return prefix; }
  public StaticRefPart getName() { return name; }

  // === Visitor ===
  public void accept(IVisitorWithAdditions visitor) {
    visitor.visitStaticRef(this, prefix, name, getLocation());
  }

  // === Others ===
  @Override
  public StaticRef clone() {
    List<StaticRefPart> newPrefix = prefix;
    StaticRefPart newName = name == null ? null : name.clone();
    return StaticRef.mk(newPrefix, newName, getLocation());
  }

  @Override
  public String toString() {
    return StringUtil.prettyPrint(this);
  }
}

