/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.errorreporting;

import ie.ucd.bon.parser.errors.ParsingError;
import ie.ucd.bon.source.SourceLocation;

import java.io.File;
import java.io.PrintStream;

public class FileNotFoundError extends ParsingError {

  private static final String message = "File not found: %s";

  public FileNotFoundError(File sourceFile) {
    //super(sourceFile, BONProblem.FILE_PROBLEM, BONProblem.UNKNOWN_CHAR_POSITION, true);
    super(SourceLocation.NO_LOCATION, true);
  }

  public void printStart(PrintStream ps) {
    //Do nothing!
  }

  @Override
  public String getMessage() {
    return String.format(message, getLocation().getSourceFile().getPath());
  }

}
