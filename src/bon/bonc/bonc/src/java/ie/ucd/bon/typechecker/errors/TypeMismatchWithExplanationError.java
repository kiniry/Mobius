/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.errors;

import ie.ucd.bon.source.SourceLocation;

public class TypeMismatchWithExplanationError extends TypeMismatchError {

  public TypeMismatchWithExplanationError(SourceLocation loc, String explanation, String desired, String actual) {
    super(loc, message(explanation, desired, actual));
  }


  private static String message(String explanation, String desired, String actual) {
    String m = explanation;
    if (actual == null) {
      m += String.format(MESSAGE1, desired);
    } else {
      m += String.format(MESSAGE2, desired, actual);
    }
    return m;
  }

}
