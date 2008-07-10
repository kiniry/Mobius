/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker;

import ie.ucd.bon.errorreporting.BONError;
import ie.ucd.bon.source.SourceLocation;

import java.io.File;

public abstract class TypeCheckingError extends BONError {

//  public TypeCheckingError(File sourceFile, int lineNumber, int charPosition) {
//    super(sourceFile, lineNumber, charPosition);
//  }
  
  public TypeCheckingError(SourceLocation loc) {
    super(loc);
  }
}
