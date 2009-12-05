/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.errors;

import ie.ucd.bon.source.SourceLocation;

public class NoParentDeclaresFeatureError extends TypeCheckingError {

  private static final String MESSAGE = "No parent class of %s declares a feature named %s. This feature cannot be %s.";
  private final String message;

  public NoParentDeclaresFeatureError(SourceLocation sourceLoc, String featureName, String className, String mod) {
    super(sourceLoc);
    message = String.format(MESSAGE, className, featureName, mod);
  }

  @Override
  public String getMessage() {
    return message;
  }

}
