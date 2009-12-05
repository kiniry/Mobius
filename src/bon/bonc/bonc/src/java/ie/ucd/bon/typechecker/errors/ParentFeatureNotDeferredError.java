/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.errors;

import ie.ucd.bon.source.SourceLocation;

public class ParentFeatureNotDeferredError extends TypeCheckingError {

  private static final String MESSAGE = "Feature %s is effective, but feature %s in parent class %s is not deferred.";
  private final String message;

  public ParentFeatureNotDeferredError(SourceLocation sourceLoc, String featureName, String parentName) {
    super(sourceLoc);
    message = String.format(MESSAGE, featureName, featureName, parentName);
  }

  @Override
  public String getMessage() {
    return message;
  }

}
