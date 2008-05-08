/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.errors;

import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.typechecker.TypeCheckingWarning;

public class DuplicateSuperclassWarning extends TypeCheckingWarning {

  private static final String message = "Duplicate definition of %s as superclass of %s";

  private final String className;
  private final String superClassName;
  
  public DuplicateSuperclassWarning(SourceLocation loc, String className, String superClassName) {
    super(loc);
    this.className = className;
    this.superClassName = superClassName;
  }

  @Override
  public String getMessage() {
    return String.format(message, className, superClassName);
  }
  
  

}
