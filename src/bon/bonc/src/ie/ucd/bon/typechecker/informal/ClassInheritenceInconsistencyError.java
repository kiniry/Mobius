/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.informal;

import java.io.File;

import ie.ucd.bon.errorreporting.BONProblem;
import ie.ucd.bon.parser.SourceLocation;
import ie.ucd.bon.typechecker.TypeCheckingError;

public class ClassInheritenceInconsistencyError extends TypeCheckingError {

  private static final String message = "%s %s does not declare inheritence from %s, as in the %s of %s";
  
  private final String itemType;
  private final String itemName;
  private final String superName;
  private final String noMatchingItemType;
  
  public ClassInheritenceInconsistencyError(File sourceFile, int lineNumber, int charPosition, 
      String itemType, String itemName, String superName, String noMatchingItemType) {
    super(sourceFile, lineNumber, charPosition);
    this.itemType = itemType;
    this.itemName = itemName;
    this.superName = superName;
    this.noMatchingItemType = noMatchingItemType;
  }

  public ClassInheritenceInconsistencyError(SourceLocation loc, 
      String itemType, String itemName, String superName, String noMatchingItemType) {
    super(loc);
    this.itemType = itemType;
    this.itemName = itemName;
    this.superName = superName;
    this.noMatchingItemType = noMatchingItemType;
  }

  @Override
  public int compareTo(BONProblem o) {
    int superCompare = super.compareTo(o);
    if (superCompare != 0) {
      return superCompare;
    }

    //Should be checked above, but just in case:
    //Using -1 as order shouldn't really matter if it's gotten to here
    if (o instanceof ClassInheritenceInconsistencyError) {
      return getMessage().equals(o.getMessage()) ? 0 : -1;
    } else {
      return -1;
    }
  }

  @Override
  public String getMessage() {
    return String.format(message, itemType, itemName, superName, noMatchingItemType, itemName);
  }
  
  
  
}
