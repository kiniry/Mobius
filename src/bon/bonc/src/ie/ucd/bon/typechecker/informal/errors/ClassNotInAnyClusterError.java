/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.informal.errors;

import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.typechecker.TypeCheckingError;

public class ClassNotInAnyClusterError extends TypeCheckingError {

  private static final String message = "Class %s does not appear in any cluster chart in this system";

  private final String className;

  public ClassNotInAnyClusterError(SourceLocation loc, String className) {
    super(loc);
    this.className = className;
  }

  @Override
  public String getMessage() {
    return String.format(message, className);
  }
  
   
  
}
