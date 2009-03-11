/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.informal;

import ie.ucd.bon.errorreporting.BONProblem;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.typechecker.TypeCheckingError;

public class ClassInheritanceInconsistencyError extends TypeCheckingError {

  private static final String message = "%s %s does not declare inheritance from %s, as in the %s of %s";
  
  private final String itemType;
  private final String itemName;
  private final String superName;
  private final String noMatchingItemType;

  public ClassInheritanceInconsistencyError(SourceLocation loc, 
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
    if (o instanceof ClassInheritanceInconsistencyError) {
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
