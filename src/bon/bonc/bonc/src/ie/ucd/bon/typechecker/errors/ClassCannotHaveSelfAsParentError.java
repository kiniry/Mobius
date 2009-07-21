/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.errors;

import ie.ucd.bon.source.SourceLocation;

public class ClassCannotHaveSelfAsParentError extends TypeCheckingError {

  private static final String message = "Class %s cannot have itself as a parent";
  
  private final String className;

  public ClassCannotHaveSelfAsParentError(SourceLocation loc, String className) {
    super(loc);
    this.className = className;
  }

  @Override
  public String getMessage() {
    return String.format(message, className);
  }

  
  
}
