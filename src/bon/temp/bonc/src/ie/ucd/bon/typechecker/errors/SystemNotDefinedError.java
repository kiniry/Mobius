/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.errors;

import ie.ucd.bon.errorreporting.BONProblem;
import ie.ucd.bon.typechecker.TypeCheckingError;

public class SystemNotDefinedError extends TypeCheckingError {

  private static final String message = "No system was defined";
  
  public SystemNotDefinedError() {
    super(null, BONProblem.GENERAL_PROBLEM, BONProblem.UNKNOWN_CHAR_POSITION);
  }

  @Override
  public String getMessage() {
    return message;
  }
  
  

}
