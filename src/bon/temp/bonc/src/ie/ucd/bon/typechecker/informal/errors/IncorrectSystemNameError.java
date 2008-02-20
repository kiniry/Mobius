/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.informal.errors;

import java.io.File;

import ie.ucd.bon.parser.SourceLocation;
import ie.ucd.bon.typechecker.TypeCheckingError;

public class IncorrectSystemNameError extends TypeCheckingError {

  private static final String message = "Incorrect system name \"%s\" (actual system %s defined at %s:%s)";
  
  private final String incorrectSystemName;
  private final String realSystemName;
  private final String systemFilePath;
  private final int systemLineNumber;
  
  public IncorrectSystemNameError(File sourceFile, int lineNumber, int charPosition, String incorrectSystemName, String realSystemName, String systemFilePath, int systemLineNumber) {
    super(sourceFile, lineNumber, charPosition);
    this.incorrectSystemName = incorrectSystemName;
    this.realSystemName = realSystemName;
    this.systemFilePath = systemFilePath;
    this.systemLineNumber = systemLineNumber;
  }

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
