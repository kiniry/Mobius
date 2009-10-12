/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.parser.errors;

import ie.ucd.bon.errorreporting.BONWarning;
import ie.ucd.bon.source.SourceLocation;

public abstract class ParsingWarning extends BONWarning {

  public ParsingWarning(SourceLocation sourceLoc, String message) {
    super(sourceLoc);
  }

}
