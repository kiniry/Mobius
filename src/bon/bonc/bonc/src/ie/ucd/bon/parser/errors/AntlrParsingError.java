/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.parser.errors;

import ie.ucd.bon.source.SourceLocation;

public class AntlrParsingError extends ParsingError {

  private final String message;

  public AntlrParsingError(SourceLocation sourceLoc, String message, boolean isSevere) {
    super(sourceLoc, isSevere);
    this.message = message;
  }

  @Override
  public String getMessage() {
    return message;
  }
}
