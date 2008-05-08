/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.errors;

import java.io.File;

import ie.ucd.bon.parser.SourceLocation;
import ie.ucd.bon.typechecker.FeatureSpecificationInstance;
import ie.ucd.bon.typechecker.TypeCheckingError;

public class DuplicateFeatureDefinitionError extends TypeCheckingError {

  private static final String message = "Duplicate definition of feature %s in class %s (Other definition - %s:%s)";

  private final String featureName;
  private final String className;
  private final File otherFeatureFile;
  private final int otherFeatureLineNumber;
  
  public DuplicateFeatureDefinitionError(SourceLocation loc, FeatureSpecificationInstance other) {
    super(loc);
    this.featureName = other.getName();
    this.className = other.getClassName();
    this.otherFeatureFile = other.getSourceLocation().getSourceFile();
    this.otherFeatureLineNumber = other.getSourceLocation().getLineNumber();
  }

  //Testing
  public DuplicateFeatureDefinitionError(SourceLocation loc, String featureName, String className, File otherFeatureFile, int otherFeatureLineNumber) {
    super(loc);
    this.featureName = featureName;
    this.className = className;
    this.otherFeatureFile = otherFeatureFile;
    this.otherFeatureLineNumber = otherFeatureLineNumber;
  }

  @Override
  public String getMessage() {
    return String.format(message, featureName, className, getFilePath(otherFeatureFile), otherFeatureLineNumber);
  }
  
  
  
}
