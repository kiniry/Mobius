/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.errors;

import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.typechecker.TypeCheckingError;
import ie.ucd.bon.typechecker.informal.SystemChartDefinition;

import java.io.File;

public class DuplicateSystemDefinitionError extends TypeCheckingError {

  private static String message = "The system has already been defined (System %s - %s:%s)";
  
  private final String systemName;
  private final File otherSystemFile;
  private final int otherSystemLineNumber;
  
  public DuplicateSystemDefinitionError(SourceLocation loc, SystemChartDefinition otherSystem) {
    super(loc);
    this.systemName = otherSystem.getSystemName();
    this.otherSystemFile = otherSystem.getSourceLocation().getSourceFile();
    this.otherSystemLineNumber = otherSystem.getSourceLocation().getLineNumber();
  }
  
  //Testing
  public DuplicateSystemDefinitionError(SourceLocation loc, String systemName, File otherSystemFile, int otherSystemLineNumber) {
    super(loc);
    this.systemName = systemName;
    this.otherSystemFile = otherSystemFile;
    this.otherSystemLineNumber = otherSystemLineNumber;
  }

  @Override
  public String getMessage() {
    return String.format(message, systemName, SourceLocation.getFilePath(otherSystemFile), otherSystemLineNumber);
  }
  
}
