/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.errors;

import ie.ucd.bon.source.SourceLocation;

public class TypeMismatchError extends TypeCheckingError {

  private static final String message1 = "Expected %s.";
  private static final String message2 = "Expected %s but found %s.";

  private final String err;

  public TypeMismatchError(SourceLocation loc, String desired, String actual) {
    super(loc);
    err = String.format(message2, desired, actual);
  }
  
  public TypeMismatchError(SourceLocation loc, String desired) {
    super(loc);
    err = String.format(message1, desired);
  }

  public String getMessage() {
    return err;
  }
  
  

}
