/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker;

import java.io.File;

import org.antlr.runtime.Token;

import ie.ucd.bon.parser.SourceLocation;

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

  public String getClassName() {
    return featureSpec.getClassName();
  }
  
  public boolean isDeferred() {
    return featureSpec.isDeferred();
  }

  public SourceLocation getSourceLocation() {
    return loc;
  }

  public FeatureSpecification getFeatureSpec() {
    return featureSpec;
  }
  
  
}
