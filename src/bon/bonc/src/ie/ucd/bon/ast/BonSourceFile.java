
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.ast.AstNode;

public class BonSourceFile extends AstNode {


  private final Indexing indexing;

  private final List<SpecificationElement> bonSpecification;

  private final SourceLocation location;

  // === Constructors and Factories ===
  protected BonSourceFile(List<SpecificationElement> bonSpecification, Indexing indexing) {
    this(bonSpecification,indexing, null);    
  }

  protected BonSourceFile(List<SpecificationElement> bonSpecification, Indexing indexing, SourceLocation location) {
    
    assert location != null;
    this.location = location;
    this.bonSpecification = bonSpecification; assert bonSpecification != null;
    this.indexing = indexing; 
    
  }
  
  public static BonSourceFile mk(List<SpecificationElement> bonSpecification, Indexing indexing) {
    return new BonSourceFile(bonSpecification, indexing);
  }

  public static BonSourceFile mk(List<SpecificationElement> bonSpecification, Indexing indexing, SourceLocation location) {
    return new BonSourceFile(bonSpecification, indexing, location);
  }

  // === Accessors ===

  public List<SpecificationElement> getBonSpecification() { return bonSpecification; }
  public Indexing getIndexing() { return indexing; }

  // === Others ===
  @Override
  public BonSourceFile clone() {
    List<SpecificationElement> newBonSpecification = bonSpecification;
    Indexing newIndexing = indexing == null ? null : indexing.clone();
    
    return BonSourceFile.mk(newBonSpecification, newIndexing, location);
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("BonSourceFile ast node: ");
    
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

