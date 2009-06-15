/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.errors;

import ie.ucd.bon.errorreporting.BONError;
import ie.ucd.bon.source.SourceLocation;

public abstract class TypeCheckingError extends BONError {
  
  public TypeCheckingError(SourceLocation loc) {
    super(loc);
  }
}
