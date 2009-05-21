
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.ast.AstNode;

public class ClassInterface extends AstNode {


  private final Indexing indexing;

  private final List<Feature> features;
  private final List<BONType> parents;
  private final List<Expression> invariant;

  private final SourceLocation location;

  // === Constructors and Factories ===
  protected ClassInterface(List<Feature> features, List<BONType> parents, List<Expression> invariant, Indexing indexing) {
    this(features,parents,invariant,indexing, null);    
  }

  protected ClassInterface(List<Feature> features, List<BONType> parents, List<Expression> invariant, Indexing indexing, SourceLocation location) {
    
    assert location != null;
    this.location = location;
    this.features = features; assert features != null;
    this.parents = parents; assert parents != null;
    this.invariant = invariant; 
    this.indexing = indexing; 
    
  }
  
  public static ClassInterface mk(List<Feature> features, List<BONType> parents, List<Expression> invariant, Indexing indexing) {
    return new ClassInterface(features, parents, invariant, indexing);
  }

  public static ClassInterface mk(List<Feature> features, List<BONType> parents, List<Expression> invariant, Indexing indexing, SourceLocation location) {
    return new ClassInterface(features, parents, invariant, indexing, location);
  }
  
  public SourceLocation getLocation() {
    return location;
  }

  // === Accessors ===

  public List<Feature> getFeatures() { return features; }
  public List<BONType> getParents() { return parents; }
  public List<Expression> getInvariant() { return invariant; }
  public Indexing getIndexing() { return indexing; }

  // === Others ===
  @Override
  public ClassInterface clone() {
    List<Feature> newFeatures = features;
    List<BONType> newParents = parents;
    List<Expression> newInvariant = invariant;
    Indexing newIndexing = indexing == null ? null : indexing.clone();
    
    return ClassInterface.mk(newFeatures, newParents, newInvariant, newIndexing, location);
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

