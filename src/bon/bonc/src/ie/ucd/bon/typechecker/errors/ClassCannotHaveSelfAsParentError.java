/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.errors;

import java.io.File;

import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.typechecker.TypeCheckingError;

public class ClassCannotHaveSelfAsParentError extends TypeCheckingError {

  private static final String message = "Class %s cannot have itself as a parent";
  
  private final String className;
  
  public ClassCannotHaveSelfAsParentError(File sourceFile, int lineNumber, int charPosition, String className) {
    super(sourceFile, lineNumber, charPosition);
    this.className = className;
  }

  public ClassCannotHaveSelfAsParentError(SourceLocation loc, String className) {
    super(loc);
    this.className = className;
  }

  @Override
  public String getMessage() {
    return String.format(message, className);
  }

  
  
}
