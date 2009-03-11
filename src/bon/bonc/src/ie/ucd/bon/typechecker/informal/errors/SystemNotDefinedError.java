/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.informal.errors;

import ie.ucd.bon.typechecker.TypeCheckingError;

public class SystemNotDefinedError extends TypeCheckingError {

  private static final String message = "No system was defined";
  
  public SystemNotDefinedError() {
    super(null);
  }

  @Override
  public String getMessage() {
    return message;
  }
  
  

}
