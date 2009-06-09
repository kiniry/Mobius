/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.errors;

import ie.ucd.bon.ast.FeatureSpecification;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.typechecker.FeatureSpecificationInstance;
import ie.ucd.bon.typechecker.TypeCheckingError;

import java.io.File;

public class DuplicateFeatureDefinitionError extends TypeCheckingError {

  private static final String message = "Duplicate definition of feature %s in class %s (Other definition - %s:%s)";

  private final String featureName;
  private final String className;
  private final File otherFeatureFile;
  private final int otherFeatureLineNumber;
  
  public DuplicateFeatureDefinitionError(SourceLocation loc, FeatureSpecificationInstance other) {
    super(loc);
    this.featureName = other.getName();
    this.className = other.getFeatureSpec().getClassName();
    this.otherFeatureFile = other.getSourceLocation().getSourceFile();
    this.otherFeatureLineNumber = other.getSourceLocation().getLineNumber();
  }
  
  public DuplicateFeatureDefinitionError(SourceLocation loc, String className, String featureName, FeatureSpecification other) {
    super(loc);
    this.featureName = featureName;
    this.className = className;
    this.otherFeatureFile = other.getLocation().getSourceFile();
    this.otherFeatureLineNumber = other.getLocation().getLineNumber();
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
    return String.format(message, featureName, className, SourceLocation.getFilePath(otherFeatureFile), otherFeatureLineNumber);
  }
  
  
  
}
