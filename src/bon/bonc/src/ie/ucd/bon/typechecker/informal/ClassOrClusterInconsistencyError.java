/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.informal;

import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.typechecker.TypeCheckingError;

import java.io.File;

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
  
  public ClassOrClusterInconsistencyError(File sourceFile, int lineNumber, int charPosition, String itemType, String itemName, String noMatchingItemType) {
    super(sourceFile, lineNumber, charPosition);
    this.itemType = itemType;
    this.itemName = itemName;
    this.noMatchingItemType = noMatchingItemType;
  }

  @Override
  public String getMessage() {
    return String.format(message, itemType, itemName, noMatchingItemType);
  }
  
  
  
}
