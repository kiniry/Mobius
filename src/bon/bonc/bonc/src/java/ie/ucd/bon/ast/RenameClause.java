
/**
 * Copyright (c) 2007-2010, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 *
 * This class is generated automatically from normal_classes.tpl.
 * Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.util.StringUtil;

public class RenameClause extends AstNode {


  public final ClassName className;
  public final FeatureName featureName;



  // === Constructors and Factories ===
  protected RenameClause(ClassName className, FeatureName featureName, SourceLocation location) {
    super(location);
    this.className = className; assert className != null;
    this.featureName = featureName; assert featureName != null;
  }

  public static RenameClause mk(ClassName className, FeatureName featureName, SourceLocation location) {
    return new RenameClause(className, featureName, location);
  }

  // === Accessors ===

  public ClassName getClassName() { return className; }
  public FeatureName getFeatureName() { return featureName; }

  // === Visitor ===
  public void accept(IVisitorWithAdditions visitor) {
    visitor.visitRenameClause(this, className, featureName, getLocation());
  }

  // === Others ===
  @Override
  public RenameClause clone() {
    ClassName newClassName = className == null ? null : className.clone();
    FeatureName newFeatureName = featureName == null ? null : featureName.clone();
    return RenameClause.mk(newClassName, newFeatureName, getLocation());
  }

  @Override
  public String toString() {
    return StringUtil.prettyPrint(this);
  }
}

