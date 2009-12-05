/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.errors;

import ie.ucd.bon.source.SourceLocation;

public class ParentFeatureIsDeferredError extends TypeCheckingError {

  private static final String MESSAGE = "Feature %s cannot be redefined, as feature %s in parent class %s is deferred.";
  private final String message;

  public ParentFeatureIsDeferredError(SourceLocation sourceLoc, String featureName, String parentName) {
    super(sourceLoc);
    message = String.format(MESSAGE, featureName, featureName, parentName);
  }

  @Override
  public String getMessage() {
    return message;
  }

}
