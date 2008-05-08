/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.informal.errors;

import java.io.File;

import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.typechecker.TypeCheckingError;

public class ClusterNotInAnyClusterOrSystemError extends TypeCheckingError {

  private static final String message = "Cluster %s does not appear in any cluster chart or in the system chart";
  
  private final String clusterName;
  
  public ClusterNotInAnyClusterOrSystemError(File sourceFile, int lineNumber, int charPosition, String clusterName) {
    super(sourceFile, lineNumber, charPosition);
    this.clusterName = clusterName;
  }

  public ClusterNotInAnyClusterOrSystemError(SourceLocation loc, String clusterName) {
    super(loc);
    this.clusterName = clusterName;
  }

  @Override
  public String getMessage() {
    return String.format(message, clusterName);
  }

  
  
}
