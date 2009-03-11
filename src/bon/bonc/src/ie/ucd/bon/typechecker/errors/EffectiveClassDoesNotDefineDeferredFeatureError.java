/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.errors;

import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.typechecker.TypeCheckingError;

public class EffectiveClassDoesNotDefineDeferredFeatureError extends TypeCheckingError {
  
  
  private static final String message = "%s is effective and does not define deferred feature %s from %s";
  
  private final String featureName;
  private final String className;
  private final String parentName;
  
  public EffectiveClassDoesNotDefineDeferredFeatureError(SourceLocation loc, String featureName, String className, String parentName) {
    super(loc);
    this.featureName = featureName;
    this.className = className;
    this.parentName = parentName;
  }

  @Override
  public String getMessage() {
    return String.format(message, className, featureName, parentName);
  }

}
