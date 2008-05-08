/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.errors;

import ie.ucd.bon.parser.SourceLocation;
import ie.ucd.bon.typechecker.TypeCheckingError;

import java.util.Collection;

public class CycleInRelationsError extends TypeCheckingError {

  private static final String message1 = "%s %s has a cycle in its %s";
  private static final String message2 = "%s %s has a cycle in its %s (%s)";
  
  private final String itemType;
  private final String itemName;
  private final String cycleString;
  private final String relationType;
  
  /*public CycleInRelationsError(File sourceFile, int lineNumber, int charPosition, String itemType, String itemName, Collection<String> cycle, String relationType) {
    super(sourceFile, lineNumber, charPosition);
    this.itemType = itemType;
    this.itemName = itemName;
    this.cycleString = convertToCycleString(cycle, itemName);
    this.relationType = relationType;
  }*/

  public CycleInRelationsError(SourceLocation loc, String itemType, String itemName, Collection<String> cycle, String relationType) {
    super(loc);
    this.itemType = itemType;
    this.itemName = itemName;
    this.cycleString = convertToCycleString(cycle, itemName);
    this.relationType = relationType;
  }
  
  //For testing
  public CycleInRelationsError(SourceLocation loc, String itemType, String itemName, String cycle, String relationType) {
    super(loc);
    this.itemType = itemType;
    this.itemName = itemName;
    this.cycleString = cycle;
    this.relationType = relationType;
  }
  
  private static String convertToCycleString(Collection<String> cycle, String start) {
    StringBuilder sb = new StringBuilder();
    for (String name : cycle) {
      sb.append(name);
      sb.append("->");
    }
    sb.append(start);
    return sb.toString();
  }

  @Override
  public String getMessage() {
    if (cycleString == null) {
      return String.format(message1, itemType, itemName, relationType);
    } else {
      return String.format(message2, itemType, itemName, relationType, cycleString);
    }
  }
  
}
