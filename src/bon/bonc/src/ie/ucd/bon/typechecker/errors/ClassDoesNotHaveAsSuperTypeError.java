/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.errors;

import ie.ucd.bon.source.SourceLocation;

public class ClassDoesNotHaveAsSuperTypeError extends TypeCheckingError {

  private static final String message = "Class %s does not have class %s as a supertype";
  
  private final String className;
  private final String superName;

  public ClassDoesNotHaveAsSuperTypeError(SourceLocation loc, String className, String superName) {
    super(loc);
    this.className = className;
    this.superName = superName;
  }

  @Override
  public String getMessage() {
    return String.format(message, className, superName);
  }  
  
}
