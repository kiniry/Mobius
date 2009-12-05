/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.errors;

import ie.ucd.bon.ast.Clazz;
import ie.ucd.bon.source.SourceLocation;

import java.io.File;

public class DuplicateClassDefinitionError extends TypeCheckingError {

  private static final String message = "Duplicate definition of class %s (Other definition - %s:%s)";

  private final String className;
  private final File otherClassFile;
  private final int otherClassLineNumber;

  public DuplicateClassDefinitionError(SourceLocation loc, Clazz other) {
    super(loc);
    this.className = other.getName().getName();
    this.otherClassFile = other.getLocation().getSourceFile();
    this.otherClassLineNumber = other.getLocation().getLineNumber();
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
    return String.format(message, className, SourceLocation.getFilePath(otherClassFile), otherClassLineNumber);
  }

}
