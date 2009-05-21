
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;

public class ClassInterface extends AstNode {


  private final Indexing indexing;

  private final List<Feature> features;
  private final List<BONType> parents;
  private final List<Expression> invariant;


  // === Constructors and Factories ===
  protected ClassInterface(List<Feature> features, List<BONType> parents, List<Expression> invariant, Indexing indexing, SourceLocation location) {
    super(location);
    this.features = features; assert features != null;
    this.parents = parents; assert parents != null;
    this.invariant = invariant; 
    this.indexing = indexing; 
    
  }
  
  public static ClassInterface mk(List<Feature> features, List<BONType> parents, List<Expression> invariant, Indexing indexing, SourceLocation location) {
    return new ClassInterface(features, parents, invariant, indexing, location);
  }

  // === Accessors ===

  public List<Feature> getFeatures() { return features; }
  public List<BONType> getParents() { return parents; }
  public List<Expression> getInvariant() { return invariant; }
  public Indexing getIndexing() { return indexing; }

  // === Visitor ===
  public void accept(IVisitor visitor) {
    visitor.visitClassInterface(this);
  }

  // === Others ===
  @Override
  public ClassInterface clone() {
    List<Feature> newFeatures = features;
    List<BONType> newParents = parents;
    List<Expression> newInvariant = invariant;
    Indexing newIndexing = indexing == null ? null : indexing.clone();
    
    return ClassInterface.mk(newFeatures, newParents, newInvariant, newIndexing, getLocation());
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("ClassInterface ast node: ");
    
    sb.append("features = ");
    sb.append(features);
    sb.append(", ");
    
    sb.append("parents = ");
    sb.append(parents);
    sb.append(", ");
    
    sb.append("invariant = ");
    sb.append(invariant);
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

