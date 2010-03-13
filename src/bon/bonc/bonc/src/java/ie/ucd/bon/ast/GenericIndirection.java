
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

public class GenericIndirection extends AstNode {


  public final IndirectionElement indirectionElement;



  // === Constructors and Factories ===
  protected GenericIndirection(IndirectionElement indirectionElement, SourceLocation location) {
    super(location);
    this.indirectionElement = indirectionElement; assert indirectionElement != null;
  }

  public static GenericIndirection mk(IndirectionElement indirectionElement, SourceLocation location) {
    return new GenericIndirection(indirectionElement, location);
  }

  // === Accessors ===

  public IndirectionElement getIndirectionElement() { return indirectionElement; }

  // === Visitor ===
  public void accept(IVisitorWithAdditions visitor) {
    visitor.visitGenericIndirection(this, indirectionElement, getLocation());
  }

  // === Others ===
  @Override
  public GenericIndirection clone() {
    IndirectionElement newIndirectionElement = indirectionElement == null ? null : indirectionElement.clone();
    return GenericIndirection.mk(newIndirectionElement, getLocation());
  }

  @Override
  public String toString() {
    return StringUtil.prettyPrint(this);
  }
}

