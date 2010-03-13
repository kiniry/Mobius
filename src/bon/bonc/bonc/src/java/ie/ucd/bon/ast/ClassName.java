
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

public class ClassName extends IndirectionElement {



  public final String name;


  // === Constructors and Factories ===
  protected ClassName(String name, SourceLocation location) {
    super(location);
    this.name = name; assert name != null;
  }

  public static ClassName mk(String name, SourceLocation location) {
    return new ClassName(name, location);
  }

  // === Accessors ===

  public String getName() { return name; }

  // === Visitor ===
  public void accept(IVisitorWithAdditions visitor) {
    visitor.visitClassName(this, name, getLocation());
  }

  // === Others ===
  @Override
  public ClassName clone() {
    String newName = name;
    return ClassName.mk(newName, getLocation());
  }

  @Override
  public String toString() {
    return StringUtil.prettyPrint(this);
  }
}

