
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.ast.AstNode;

public class IndirectionFeatureList extends IndirectionFeaturePart {



  private final List<FeatureName> featureNames;

  private final SourceLocation location;

  // === Constructors and Factories ===
  protected IndirectionFeatureList(List<FeatureName> featureNames) {
    this(featureNames, null);    
  }

  protected IndirectionFeatureList(List<FeatureName> featureNames, SourceLocation location) {
    
    assert location != null;
    this.location = location;
    this.featureNames = featureNames; 
    
  }
  
  public static IndirectionFeatureList mk(List<FeatureName> featureNames) {
    return new IndirectionFeatureList(featureNames);
  }

  public static IndirectionFeatureList mk(List<FeatureName> featureNames, SourceLocation location) {
    return new IndirectionFeatureList(featureNames, location);
  }

  // === Accessors ===

  public List<FeatureName> getFeatureNames() { return featureNames; }

  // === Others ===
  @Override
  public IndirectionFeatureList clone() {
    List<FeatureName> newFeatureNames = featureNames;
    
    return IndirectionFeatureList.mk(newFeatureNames, location);
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("IndirectionFeatureList ast node: ");
    
    sb.append("featureNames = ");
    sb.append(featureNames);
    sb.append(", ");
    
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2,sb.length());
    }
    return sb.toString();
  }
}

