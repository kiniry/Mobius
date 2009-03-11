/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker;

import ie.ucd.bon.source.SourceLocation;

public class FeatureSpecificationInstance {

  private final FeatureSpecification featureSpec;
  private final String name;
  private final SourceLocation loc;
  
  public FeatureSpecificationInstance(String name, FeatureSpecification featureSpec, SourceLocation loc) {
    this.loc = loc;
    this.name = name;
    this.featureSpec = featureSpec;
    this.featureSpec.addInstance(this);
  }

  public String getName() {
    return name;
  }

  public SourceLocation getSourceLocation() {
    return loc;
  }

  public FeatureSpecification getFeatureSpec() {
    return featureSpec;
  }
  
  
}
