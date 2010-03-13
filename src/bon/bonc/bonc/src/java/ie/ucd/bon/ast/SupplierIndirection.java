
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

public class SupplierIndirection extends ClientEntity {


  public final IndirectionFeaturePart indirectionFeaturePart;
  public final GenericIndirection genericIndirection;



  // === Constructors and Factories ===
  protected SupplierIndirection(IndirectionFeaturePart indirectionFeaturePart, GenericIndirection genericIndirection, SourceLocation location) {
    super(location);
    this.indirectionFeaturePart = indirectionFeaturePart; 
    this.genericIndirection = genericIndirection; assert genericIndirection != null;
  }

  public static SupplierIndirection mk(IndirectionFeaturePart indirectionFeaturePart, GenericIndirection genericIndirection, SourceLocation location) {
    return new SupplierIndirection(indirectionFeaturePart, genericIndirection, location);
  }

  // === Accessors ===

  public IndirectionFeaturePart getIndirectionFeaturePart() { return indirectionFeaturePart; }
  public GenericIndirection getGenericIndirection() { return genericIndirection; }

  // === Visitor ===
  public void accept(IVisitorWithAdditions visitor) {
    visitor.visitSupplierIndirection(this, indirectionFeaturePart, genericIndirection, getLocation());
  }

  // === Others ===
  @Override
  public SupplierIndirection clone() {
    IndirectionFeaturePart newIndirectionFeaturePart = indirectionFeaturePart == null ? null : indirectionFeaturePart.clone();
    GenericIndirection newGenericIndirection = genericIndirection == null ? null : genericIndirection.clone();
    return SupplierIndirection.mk(newIndirectionFeaturePart, newGenericIndirection, getLocation());
  }

  @Override
  public String toString() {
    return StringUtil.prettyPrint(this);
  }
}

