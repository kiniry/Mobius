/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.errors;

import ie.ucd.bon.source.SourceLocation;

public class DuplicateFormalGenericNameError extends TypeCheckingError {

  private static final String message = "Duplicate formal generic with name %s";

  private final String formalGenericName;

  public DuplicateFormalGenericNameError(SourceLocation loc, String formalGenericName) {
    super(loc);
    this.formalGenericName = formalGenericName;
  }

  @Override
  public String getMessage() {
    return String.format(message, formalGenericName);
  }

}
