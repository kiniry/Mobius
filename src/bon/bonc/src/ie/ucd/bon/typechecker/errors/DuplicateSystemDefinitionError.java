/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.errors;

import ie.ucd.bon.ast.ClusterChart;
import ie.ucd.bon.source.SourceLocation;

import java.io.File;

public class DuplicateSystemDefinitionError extends TypeCheckingError {

  private static String message = "The system has already been defined (System %s - %s:%s)";
  
  private final String systemName;
  private final File otherSystemFile;
  private final int otherSystemLineNumber;
  
  public DuplicateSystemDefinitionError(SourceLocation loc, ClusterChart otherSystem) {
    super(loc);
    this.systemName = otherSystem.getName();
    this.otherSystemFile = otherSystem.getLocation().getSourceFile();
    this.otherSystemLineNumber = otherSystem.getLocation().getLineNumber();
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
