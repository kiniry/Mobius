/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.informal.errors;

import ie.ucd.bon.parser.SourceLocation;
import ie.ucd.bon.typechecker.TypeCheckingError;
import ie.ucd.bon.typechecker.informal.ClusterChartDefinition;

import java.io.File;

public class DuplicateClusterChartError extends TypeCheckingError {

  private static final String message = "Duplicate cluster chart for %s (Other chart - %s:%s)";
  
  private final String clusterName;
  private final File otherChartFile;
  private final int otherChartLineNumber;
  
  public DuplicateClusterChartError(SourceLocation loc, ClusterChartDefinition other) {
    super(loc);
    this.clusterName = other.getClusterName();
    this.otherChartFile = other.getSourceLocation().getSourceFile();
    this.otherChartLineNumber = other.getSourceLocation().getLineNumber();
  }
  
  public DuplicateClusterChartError(SourceLocation loc, String clusterName, File otherChartFile, int otherLineNumber) {
    super(loc);this.clusterName = clusterName;
    this.otherChartFile = otherChartFile;
    this.otherChartLineNumber = otherLineNumber;
  }

  @Override
  public String getMessage() {
    return String.format(message, clusterName, getFilePath(otherChartFile), otherChartLineNumber);
  }
  
}
