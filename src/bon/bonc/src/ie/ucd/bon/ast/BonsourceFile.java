
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.ast.AstNode;

public class BonsourceFile extends AstNode {


  private final Indexing indexing;

  private final List<SpecificationElement> bonSpecification;

  private final SourceLocation location;

  // === Constructors and Factories ===
  protected BonsourceFile(List<SpecificationElement> bonSpecification, Indexing indexing) {
    this(bonSpecification,indexing, null);    
  }

  protected BonsourceFile(List<SpecificationElement> bonSpecification, Indexing indexing, SourceLocation location) {
    
    assert location != null;
    this.location = location;
    this.bonSpecification = bonSpecification; assert bonSpecification != null;
    this.indexing = indexing; 
    
  }
  
  public static BonsourceFile mk(List<SpecificationElement> bonSpecification, Indexing indexing) {
    return new BonsourceFile(bonSpecification, indexing);
  }

  public static BonsourceFile mk(List<SpecificationElement> bonSpecification, Indexing indexing, SourceLocation location) {
    return new BonsourceFile(bonSpecification, indexing, location);
  }

  // === Accessors ===

  public List<SpecificationElement> getBonSpecification() { return bonSpecification; }
  public Indexing getIndexing() { return indexing; }

  // === Others ===
  @Override
  public BonsourceFile clone() {
    List<SpecificationElement> newBonSpecification = bonSpecification;
    Indexing newIndexing = indexing == null ? null : indexing.clone();
    
    return BonsourceFile.mk(newBonSpecification, newIndexing, location);
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("BonsourceFile ast node: ");
    
    sb.append("bonSpecification = ");
    sb.append(bonSpecification);
    sb.append(", ");
    
    sb.append("indexing = ");
    sb.append(indexing);
    sb.append(", ");
    
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2,sb.length());
    }
    return sb.toString();
  }
}

