/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.errors;

import java.io.File;

import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.typechecker.ClusterDefinition;
import ie.ucd.bon.typechecker.TypeCheckingError;


public class DuplicateClusterDefinitionError extends TypeCheckingError {

  private static final String message = "Duplicate definition of cluster %s (Other definition - %s:%s)";
  
  private final String clusterName;
  private final File otherClusterFile;
  private final int otherClusterLineNumber;
  
  public DuplicateClusterDefinitionError(SourceLocation loc, ClusterDefinition other) {
    super(loc);
    this.clusterName = other.getName();
    this.otherClusterFile = other.getSourceLocation().getSourceFile();
    this.otherClusterLineNumber = other.getSourceLocation().getLineNumber();
  }
  
  //Testing
  public DuplicateClusterDefinitionError(SourceLocation loc, String clusterName, File otherClusterFile, int otherClusterLineNumber) {
    super(loc);
    this.clusterName = clusterName;
    this.otherClusterFile = otherClusterFile;
    this.otherClusterLineNumber = otherClusterLineNumber;
  }

  @Override
  public String getMessage() {
    return String.format(message, clusterName, SourceLocation.getFilePath(otherClusterFile), otherClusterLineNumber);
  }
}
