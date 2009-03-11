/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.parser.errors;

import ie.ucd.bon.errorreporting.BONError;
import ie.ucd.bon.source.SourceLocation;

public abstract class ParsingError extends BONError {

  private final boolean severe;

  public ParsingError(SourceLocation sourceLoc, boolean isSevere) {
    super(sourceLoc);
    this.severe = isSevere;
  }  
  
  public final boolean isSevere() {
    return severe;
  }

  @Override
  public boolean equals(Object obj) {
    return super.equals(obj);
  }
  
  
}
