/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.informal.errors;

import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.typechecker.errors.TypeCheckingError;

public class IncorrectSystemNameError extends TypeCheckingError {

  private static final String message = "Incorrect system name \"%s\" (actual system %s defined at %s:%s)";

  private final String incorrectSystemName;
  private final String realSystemName;
  private final String systemFilePath;
  private final int systemLineNumber;

  public IncorrectSystemNameError(SourceLocation loc, String incorrectSystemName, String realSystemName, String systemFilePath, int systemLineNumber) {
    super(loc);
    this.incorrectSystemName = incorrectSystemName;
    this.realSystemName = realSystemName;
    this.systemFilePath = systemFilePath;
    this.systemLineNumber = systemLineNumber;
  }

  @Override
  public String getMessage() {
    return String.format(message, incorrectSystemName, realSystemName, systemFilePath, systemLineNumber);
  }

}
