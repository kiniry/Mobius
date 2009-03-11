/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.errors;

import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.typechecker.TypeCheckingError;

public class DeferredFeatureInNonDeferredClassError extends TypeCheckingError {

  private static final String message = "Deferred feature %s declared in non-deferred class %s";
  private static final String message2 = "Deferred features %s declared in non-deferred class %s";
  
  private final String featureNames;
  private final String className;
  
  public DeferredFeatureInNonDeferredClassError(SourceLocation loc,
      String featureNames, String className) {
    super(loc);
    this.featureNames = featureNames;
    this.className = className;
  }

  @Override
  public String getMessage() {
    if (featureNames.contains(",")) {
      return String.format(message2, featureNames, className);
    } else {
      return String.format(message, featureNames, className);
    }
  }

}
