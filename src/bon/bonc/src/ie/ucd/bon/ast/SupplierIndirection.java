
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.ast.AstNode;

public class SupplierIndirection extends ClientEntity {


  private final IndirectionFeaturePart indirectionFeaturePart;
  private final GenericIndirection genericIndirection;


  private final SourceLocation location;

  // === Constructors and Factories ===
  protected SupplierIndirection(IndirectionFeaturePart indirectionFeaturePart, GenericIndirection genericIndirection) {
    this(indirectionFeaturePart,genericIndirection, null);    
  }

  protected SupplierIndirection(IndirectionFeaturePart indirectionFeaturePart, GenericIndirection genericIndirection, SourceLocation location) {
    
    assert location != null;
    this.location = location;
    this.indirectionFeaturePart = indirectionFeaturePart; 
    this.genericIndirection = genericIndirection; assert genericIndirection != null;
    
  }
  
  public static SupplierIndirection mk(IndirectionFeaturePart indirectionFeaturePart, GenericIndirection genericIndirection) {
    return new SupplierIndirection(indirectionFeaturePart, genericIndirection);
  }

  public static SupplierIndirection mk(IndirectionFeaturePart indirectionFeaturePart, GenericIndirection genericIndirection, SourceLocation location) {
    return new SupplierIndirection(indirectionFeaturePart, genericIndirection, location);
  }
  
  public SourceLocation getLocation() {
    return location;
  }

  // === Accessors ===

  public IndirectionFeaturePart getIndirectionFeaturePart() { return indirectionFeaturePart; }
  public GenericIndirection getGenericIndirection() { return genericIndirection; }

  // === Others ===
  @Override
  public SupplierIndirection clone() {
    IndirectionFeaturePart newIndirectionFeaturePart = indirectionFeaturePart == null ? null : indirectionFeaturePart.clone();
    GenericIndirection newGenericIndirection = genericIndirection == null ? null : genericIndirection.clone();
    
    return SupplierIndirection.mk(newIndirectionFeaturePart, newGenericIndirection, location);
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("SupplierIndirection ast node: ");
    
    sb.append("indirectionFeaturePart = ");
    sb.append(indirectionFeaturePart);
    sb.append(", ");
    
    sb.append("genericIndirection = ");
    sb.append(genericIndirection);
    sb.append(", ");
    
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2,sb.length());
    }
    return sb.toString();
  }
}

