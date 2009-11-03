/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.errorreporting;

import ie.ucd.bon.source.SourceLocation;

public abstract class BONError extends BONProblem {

  public BONError(SourceLocation sourceLoc) {
    super(sourceLoc);
  }

  public BONProblemType getType() {
    return BONProblemType.ERROR;
  }

}
