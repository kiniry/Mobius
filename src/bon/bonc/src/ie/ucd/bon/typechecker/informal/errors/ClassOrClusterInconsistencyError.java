/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.informal.errors;

import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.typechecker.TypeCheckingError;

public class ClassOrClusterInconsistencyError extends TypeCheckingError {

  private static final String message = "%s %s has no matching %s";
  
  private final String itemType;
  private final String itemName;
  private final String noMatchingItemType;
  
  public ClassOrClusterInconsistencyError(SourceLocation loc, String itemType, String itemName, String noMatchingItemType) {
    super(loc);
    this.itemType = itemType;
    this.itemName = itemName;
    this.noMatchingItemType = noMatchingItemType;
  }

  @Override
  public String getMessage() {
    return String.format(message, itemType, itemName, noMatchingItemType);
  }
  
}
