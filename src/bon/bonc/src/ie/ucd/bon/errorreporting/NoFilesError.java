/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.errorreporting;

import ie.ucd.bon.parser.errors.ParsingError;
import ie.ucd.bon.source.SourceLocation;

public class NoFilesError extends ParsingError {

  private static final String message = "No files to parse!";
  
  public NoFilesError() {
    super(new SourceLocation(null, SourceLocation.FILE_PROBLEM, SourceLocation.UNKNOWN_CHAR_POSITION, SourceLocation.UNKNOWN_CHAR_POSITION, SourceLocation.UNKNOWN_CHAR_POSITION), true);
  }

  @Override
  public String getMessage() {
    return message;
  }

  
  
}
