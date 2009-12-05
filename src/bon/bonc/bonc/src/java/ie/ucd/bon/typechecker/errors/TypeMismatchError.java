/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.errors;

import ie.ucd.bon.source.SourceLocation;

public class TypeMismatchError extends TypeCheckingError {

  protected static final String MESSAGE1 = "Expected %s.";
  protected static final String MESSAGE2 = "Expected %s but found %s.";

  private final String err;

  public TypeMismatchError(SourceLocation loc, String desired, String actual) {
    super(loc);
    if (actual == null) {
      err = String.format(MESSAGE1, desired);
    } else {
      err = String.format(MESSAGE2, desired, actual);
    }
  }

  protected TypeMismatchError(SourceLocation loc, String errorMessage) {
    super(loc);
    this.err = errorMessage;
  }

  public String getMessage() {
    return err;
  }

}
