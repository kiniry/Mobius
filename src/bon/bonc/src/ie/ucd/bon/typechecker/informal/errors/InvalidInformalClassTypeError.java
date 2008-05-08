/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.informal.errors;

import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.typechecker.TypeCheckingError;

public class InvalidInformalClassTypeError extends TypeCheckingError {

  private static final String message = "Invalid class type %s. Are you missing a class chart for %s?";
  
  private final String classType;
  
  public InvalidInformalClassTypeError(SourceLocation loc, String classType) {
    super(loc);
    this.classType = classType;
  }

  @Override
  public String getMessage() {
    return String.format(message, classType, classType);
  }
  
}
