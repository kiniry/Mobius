/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.errors;

import ie.ucd.bon.source.SourceLocation;

public class CannotRenameMultipleFeaturesError extends TypeCheckingError {

  private static final String message = "Cannot rename multiple features as one";

  public CannotRenameMultipleFeaturesError(SourceLocation loc) {
    super(loc);
  }

  @Override
  public String getMessage() {
    return message;
  }

}
