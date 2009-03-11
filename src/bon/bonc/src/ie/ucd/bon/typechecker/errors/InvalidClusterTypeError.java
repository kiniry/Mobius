/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.errors;

import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.typechecker.TypeCheckingError;

public class InvalidClusterTypeError extends TypeCheckingError {

  private static final String message = "Unknown cluster type %s";
  
  private final String clusterType;
  
  public InvalidClusterTypeError(SourceLocation loc, String clusterType) {
    super(loc);
    this.clusterType = clusterType;
  }

  @Override
  public String getMessage() {
    return String.format(message, clusterType);
  }
  
  
}
