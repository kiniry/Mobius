/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.clinterface;

import ie.ucd.bon.errorreporting.BONError;
import ie.ucd.bon.source.SourceLocation;

public class InvalidArgumentsError extends BONError {

  private final String message;

  public InvalidArgumentsError(String message) {
    super(SourceLocation.NO_LOCATION);
    this.message = message;
  }

  @Override
  public String getMessage() {
    return message;
  }

}
