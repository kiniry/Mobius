/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.parser.errors;

import ie.ucd.bon.errorreporting.BONWarning;
import ie.ucd.bon.parser.SourceLocation;

import java.io.File;

public abstract class ParsingWarning extends BONWarning {

  public ParsingWarning(File sourceFile, int lineNumber, int charPosition, String message) {
    super(sourceFile, lineNumber, charPosition);
  }

  public ParsingWarning(SourceLocation sourceLoc, String message) {
    super(sourceLoc);
  }
  
}
