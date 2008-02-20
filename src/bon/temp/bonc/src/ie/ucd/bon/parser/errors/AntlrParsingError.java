/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.parser.errors;

import ie.ucd.bon.parser.SourceLocation;

import java.io.File;

public class AntlrParsingError extends ParsingError {

  private final String message;
  
  public AntlrParsingError(File sourceFile, int lineNumber, int charPosition, String message, boolean isSevere) {
    super(sourceFile, lineNumber, charPosition, isSevere);
    this.message = message;
  }

  public AntlrParsingError(SourceLocation sourceLoc, String message, boolean isSevere) {
    super(sourceLoc, isSevere);
    this.message = message;
  }

  @Override
  public String getMessage() {
    return message;
  } 
  
}
