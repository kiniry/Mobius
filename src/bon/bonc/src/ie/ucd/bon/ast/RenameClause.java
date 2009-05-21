
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;

public class RenameClause extends AstNode {



  private final String className;
  private final String featureName;


  // === Constructors and Factories ===
  protected RenameClause(String className, String featureName, SourceLocation location) {
    super(location);
    this.className = className; assert className != null;
    this.featureName = featureName; assert featureName != null;
    
  }
  
  public static RenameClause mk(String className, String featureName, SourceLocation location) {
    return new RenameClause(className, featureName, location);
  }

  // === Accessors ===

  public String getClassName() { return className; }
  public String getFeatureName() { return featureName; }

  // === Visitor ===
  public void accept(IVisitor visitor) {
    visitor.visitRenameClause(this);
  }

  // === Others ===
  @Override
  public RenameClause clone() {
    String newClassName = className;
    String newFeatureName = featureName;
    
    return RenameClause.mk(newClassName, newFeatureName, getLocation());
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("RenameClause ast node: ");
    
    sb.append("className = ");
    sb.append(className);
    sb.append(", ");
    
    sb.append("featureName = ");
    sb.append(featureName);
    sb.append(", ");
    
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2,sb.length());
    }
    return sb.toString();
  }
}

