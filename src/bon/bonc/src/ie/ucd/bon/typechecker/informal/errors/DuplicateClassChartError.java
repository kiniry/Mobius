/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.informal.errors;

import ie.ucd.bon.ast.ClassChart;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.typechecker.TypeCheckingError;

import java.io.File;

public class DuplicateClassChartError extends TypeCheckingError {

  private static final String message = "Duplicate class chart for %s (Other chart - %s:%s)";
  
  private final String className;
  private final File otherChartFile;
  private final int otherChartLineNumber;
  
  public DuplicateClassChartError(SourceLocation loc, ClassChart other) {
    super(loc);
    this.className = other.getName().getName();
    this.otherChartFile = other.getLocation().getSourceFile();
    this.otherChartLineNumber = other.getLocation().getLineNumber();
  }
  
  //For the test cases...
  public DuplicateClassChartError(SourceLocation loc, String className, File otherChartFile, int otherChartLineNumber) {
    super(loc);
    this.className = className;
    this.otherChartFile = otherChartFile;
    this.otherChartLineNumber = otherChartLineNumber;
  }

  @Override
  public String getMessage() {
    return String.format(message, className, SourceLocation.getFilePath(otherChartFile), otherChartLineNumber);
  }
  
  
  
}
