
/**
  This class is generated automatically from normal_classes.tpl.
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;

public class BonSourceFile extends AstNode {


  public final Indexing indexing;

  public final List<SpecificationElement> bonSpecification;


  // === Constructors and Factories ===
  protected BonSourceFile(List<SpecificationElement> bonSpecification, Indexing indexing, SourceLocation location) {
    super(location);
    this.bonSpecification = bonSpecification; assert bonSpecification != null;
    this.indexing = indexing; 
  }

  public static BonSourceFile mk(List<SpecificationElement> bonSpecification, Indexing indexing, SourceLocation location) {
    return new BonSourceFile(bonSpecification, indexing, location);
  }

  // === Accessors ===

  public List<SpecificationElement> getBonSpecification() { return bonSpecification; }
  public Indexing getIndexing() { return indexing; }

  // === Visitor ===
  public void accept(IVisitorWithAdditions visitor) {
    visitor.visitBonSourceFile(this, bonSpecification, indexing, getLocation());
  }

  // === Others ===
  @Override
  public BonSourceFile clone() {
    List<SpecificationElement> newBonSpecification = bonSpecification;
    Indexing newIndexing = indexing == null ? null : indexing.clone();
    return BonSourceFile.mk(newBonSpecification, newIndexing, getLocation());
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
      sb.delete(sb.length()-2, sb.length());
    }
    return sb.toString();
  }
}

