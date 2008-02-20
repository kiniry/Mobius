/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker;

import ie.ucd.bon.errorreporting.BONWarning;
import ie.ucd.bon.parser.SourceLocation;

import java.io.File;

public abstract class TypeCheckingWarning extends BONWarning {

  public TypeCheckingWarning(File sourceFile, int lineNumber, int charPosition, String message) {
    super(sourceFile, lineNumber, charPosition);
  }

  public TypeCheckingWarning(SourceLocation loc) {
    super(loc);
  }

}
