/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.errors;

import ie.ucd.bon.source.SourceLocation;

public class InvalidFormalClassTypeError extends TypeCheckingError {

  private static final String message = "Unknown class type %s";
  
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
