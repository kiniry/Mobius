/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.informal.errors;

import ie.ucd.bon.ast.ClusterChart;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.typechecker.errors.TypeCheckingError;

import java.io.File;

public class DuplicateClusterChartError extends TypeCheckingError {

  private static final String message = "Duplicate cluster chart for %s (Other chart - %s:%s)";
  
  private final String clusterName;
  private final File otherChartFile;
  private final int otherChartLineNumber;
  
  public DuplicateClusterChartError(SourceLocation loc, ClusterChart other) {
    super(loc);
    this.clusterName = other.getName();
    this.otherChartFile = other.getLocation().getSourceFile();
    this.otherChartLineNumber = other.getLocation().getLineNumber();
  }
  
  public DuplicateClusterChartError(SourceLocation loc, String clusterName, File otherChartFile, int otherLineNumber) {
    super(loc);this.clusterName = clusterName;
    this.otherChartFile = otherChartFile;
    this.otherChartLineNumber = otherLineNumber;
  }

  @Override
  public String getMessage() {
    return String.format(message, clusterName, SourceLocation.getFilePath(otherChartFile), otherChartLineNumber);
  }
  
}
