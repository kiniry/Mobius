
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.ast.AstNode;

public class Feature extends AstNode {



  private final List<FeatureSpecification> featureSpecifications;
  private final List<String> selectiveExport;
  private final String comment;

  private final SourceLocation location;

  // === Constructors and Factories ===
  protected Feature(List<FeatureSpecification> featureSpecifications, List<String> selectiveExport, String comment) {
    this(featureSpecifications,selectiveExport,comment, null);    
  }

  protected Feature(List<FeatureSpecification> featureSpecifications, List<String> selectiveExport, String comment, SourceLocation location) {
    
    assert location != null;
    this.location = location;
    this.featureSpecifications = featureSpecifications; assert featureSpecifications != null;
    this.selectiveExport = selectiveExport; 
    this.comment = comment; 
    
  }
  
  public static Feature mk(List<FeatureSpecification> featureSpecifications, List<String> selectiveExport, String comment) {
    return new Feature(featureSpecifications, selectiveExport, comment);
  }

  public static Feature mk(List<FeatureSpecification> featureSpecifications, List<String> selectiveExport, String comment, SourceLocation location) {
    return new Feature(featureSpecifications, selectiveExport, comment, location);
  }

  // === Accessors ===

  public List<FeatureSpecification> getFeatureSpecifications() { return featureSpecifications; }
  public List<String> getSelectiveExport() { return selectiveExport; }
  public String getComment() { return comment; }

  // === Others ===
  @Override
  public Feature clone() {
    List<FeatureSpecification> newFeatureSpecifications = featureSpecifications;
    List<String> newSelectiveExport = selectiveExport;
    String newComment = comment;
    
    return Feature.mk(newFeatureSpecifications, newSelectiveExport, newComment, location);
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("Feature ast node: ");
    
    sb.append("featureSpecifications = ");
    sb.append(featureSpecifications);
    sb.append(", ");
    
    sb.append("selectiveExport = ");
    sb.append(selectiveExport);
    sb.append(", ");
    
    sb.append("comment = ");
    sb.append(comment);
    sb.append(", ");
    
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2,sb.length());
    }
    return sb.toString();
  }
}

