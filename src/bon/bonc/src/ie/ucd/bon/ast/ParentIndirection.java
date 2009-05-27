
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;

public class ParentIndirection extends ClientEntity {


  private final GenericIndirection genericIndirection;



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
  public void accept(IVisitor visitor) {
    visitor.visitParentIndirection(this, genericIndirection);
  }

  // === Others ===
  @Override
  public ParentIndirection clone() {
    GenericIndirection newGenericIndirection = genericIndirection == null ? null : genericIndirection.clone();
    
    return ParentIndirection.mk(newGenericIndirection, getLocation());
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("ParentIndirection ast node: ");
    
    sb.append("genericIndirection = ");
    sb.append(genericIndirection);
    sb.append(", ");
    
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2,sb.length());
    }
    return sb.toString();
  }
}

