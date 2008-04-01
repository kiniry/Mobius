/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.errors;

import ie.ucd.bon.parser.SourceLocation;
import ie.ucd.bon.typechecker.TypeCheckingError;

public class InvalidFormalClassTypeError extends TypeCheckingError {

  private static final String message = "Invalid class type %s";
  
  private final String classType;
  
  public InvalidFormalClassTypeError(SourceLocation loc, String classType) {
    super(loc);
    this.classType = classType;
  }

  @Override
  public String getMessage() {
    return String.format(message, classType);
  }
  
}
