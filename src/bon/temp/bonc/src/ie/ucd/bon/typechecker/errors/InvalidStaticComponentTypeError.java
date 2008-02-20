/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.errors;

import ie.ucd.bon.parser.SourceLocation;
import ie.ucd.bon.typechecker.TypeCheckingError;

public class InvalidStaticComponentTypeError extends TypeCheckingError {

  private static final String message = "Invalid component type %s (%s is neither a class nor a cluster)";
  
  private final String componentName;
  
  public InvalidStaticComponentTypeError(SourceLocation loc, String componentName) {
    super(loc);
    this.componentName = componentName;
  }

  @Override
  public String getMessage() {
    return String.format(message, componentName, componentName);
  }
  
  
  
}
