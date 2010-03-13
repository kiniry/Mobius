
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

public class ParentIndirection extends ClientEntity {


  public final GenericIndirection genericIndirection;



  // === Constructors and Factories ===
  protected ParentIndirection(GenericIndirection genericIndirection, SourceLocation location) {
    super(location);
    this.genericIndirection = genericIndirection; assert genericIndirection != null;
  }

  public static ParentIndirection mk(GenericIndirection genericIndirection, SourceLocation location) {
    return new ParentIndirection(genericIndirection, location);
  }

  // === Accessors ===

  public GenericIndirection getGenericIndirection() { return genericIndirection; }

  // === Visitor ===
  public void accept(IVisitorWithAdditions visitor) {
    visitor.visitParentIndirection(this, genericIndirection, getLocation());
  }

  // === Others ===
  @Override
  public ParentIndirection clone() {
    GenericIndirection newGenericIndirection = genericIndirection == null ? null : genericIndirection.clone();
    return ParentIndirection.mk(newGenericIndirection, getLocation());
  }

  @Override
  public String toString() {
    return StringUtil.prettyPrint(this);
  }
}

