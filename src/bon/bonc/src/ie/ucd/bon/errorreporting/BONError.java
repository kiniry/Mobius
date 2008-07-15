/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.errorreporting;

import ie.ucd.bon.source.SourceLocation;

public abstract class BONError extends BONProblem {

  public BONError(SourceLocation sourceLoc) {
    super(sourceLoc);
  }

  @Override
  public final boolean isError() {
    return true;
  }

  @Override
  public final boolean isWarning() {
    return false;
  }  
  
}
