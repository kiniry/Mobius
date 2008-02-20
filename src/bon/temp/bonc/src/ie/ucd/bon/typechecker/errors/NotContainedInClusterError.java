/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.errors;

import ie.ucd.bon.parser.SourceLocation;
import ie.ucd.bon.typechecker.TypeCheckingError;

public class NotContainedInClusterError extends TypeCheckingError {
 
  private static final String message1 = "Class %s is not contained in cluster %s";
  private static final String message2 = "Cluster %s is not contained in cluster %s";
  
  private final String componentName;
  private final boolean isClass;
  private final String clusterName;
  
  public NotContainedInClusterError(SourceLocation loc, String componentName, boolean isClass, String clusterName) {
    super(loc);
    this.componentName = componentName;
    this.isClass = isClass;
    this.clusterName = clusterName;
  }

  @Override
  public String getMessage() {
    if (isClass) {
      return String.format(message1, componentName, clusterName);
    } else {
      return String.format(message2, componentName, clusterName);
    }
  }  
  
}
