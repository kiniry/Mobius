
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

public class IndirectionFeatureList extends IndirectionFeaturePart {



  public final List<FeatureName> featureNames;


  // === Constructors and Factories ===
  protected IndirectionFeatureList(List<FeatureName> featureNames, SourceLocation location) {
    super(location);
    this.featureNames = featureNames; assert featureNames != null;
  }

  public static IndirectionFeatureList mk(List<FeatureName> featureNames, SourceLocation location) {
    return new IndirectionFeatureList(featureNames, location);
  }

  // === Accessors ===

  public List<FeatureName> getFeatureNames() { return featureNames; }

  // === Visitor ===
  public void accept(IVisitorWithAdditions visitor) {
    visitor.visitIndirectionFeatureList(this, featureNames, getLocation());
  }

  // === Others ===
  @Override
  public IndirectionFeatureList clone() {
    List<FeatureName> newFeatureNames = featureNames;
    return IndirectionFeatureList.mk(newFeatureNames, getLocation());
  }

  @Override
  public String toString() {
    return StringUtil.prettyPrint(this);
  }
}

