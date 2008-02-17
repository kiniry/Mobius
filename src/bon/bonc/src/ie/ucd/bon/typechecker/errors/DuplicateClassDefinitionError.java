/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.errors;

import ie.ucd.bon.parser.SourceLocation;
import ie.ucd.bon.typechecker.ClassDefinition;
import ie.ucd.bon.typechecker.TypeCheckingError;

import java.io.File;

public class DuplicateClassDefinitionError extends TypeCheckingError {

  private static final String message = "Duplicate definition of class %s (Other definition - %s:%s)";
  
  private final String className;
  private final File otherClassFile;
  private final int otherClassLineNumber;
  
  public DuplicateClassDefinitionError(SourceLocation loc, ClassDefinition other) {
    super(loc);
    this.className = other.getClassName();
    this.otherClassFile = other.getSourceLocation().getSourceFile();
    this.otherClassLineNumber = other.getSourceLocation().getLineNumber();
  }
  
  //Testing
  public DuplicateClassDefinitionError(SourceLocation loc, String className, File otherClassFile, int otherClassLineNumber) {
    super(loc);
    this.className = className;
    this.otherClassFile = otherClassFile;
    this.otherClassLineNumber = otherClassLineNumber;
  }

  @Override
  public String getMessage() {
    return String.format(message, className, otherClassFile.getPath(), otherClassLineNumber);
  }

}
