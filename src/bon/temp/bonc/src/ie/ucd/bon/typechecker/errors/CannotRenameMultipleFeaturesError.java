/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.errors;

import java.io.File;

import ie.ucd.bon.parser.SourceLocation;
import ie.ucd.bon.typechecker.TypeCheckingError;

public class CannotRenameMultipleFeaturesError extends TypeCheckingError {

  private static final String message = "Cannot rename multiple features as one";
  
  public CannotRenameMultipleFeaturesError(File sourceFile, int lineNumber, int charPosition) {
    super(sourceFile, lineNumber, charPosition);
  }

  public CannotRenameMultipleFeaturesError(SourceLocation loc) {
    super(loc);
  }

  @Override
  public String getMessage() {
    return message;
  }

  
  
}
