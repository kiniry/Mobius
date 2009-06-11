/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.errors;

import ie.ucd.bon.ast.ClassChart;
import ie.ucd.bon.ast.ClusterChart;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.typechecker.TypeCheckingError;

import java.util.Collection;

public class CycleInRelationsError extends TypeCheckingError {

  private static final String message1 = "%s %s has a cycle in its %s";
  private static final String message2 = "%s %s has a cycle in its %s (%s)";
  
  private final String itemType;
  private final String item;
  private final String cycleString;
  private final String relationType;

  public CycleInRelationsError(SourceLocation loc, String itemType, String item, Collection<String> cycle, String relationType) {
    super(loc);
    this.itemType = itemType;
    this.item = item;
    this.cycleString = convertToCycleString(cycle, item);
    this.relationType = relationType;
  }
  
  public CycleInRelationsError(SourceLocation loc, String itemType, ClassChart item, Collection<ClassChart> cycle, String relationType) {
    super(loc);
    this.itemType = itemType;
    this.item = item.getName().getName();
    this.cycleString = convertToCycleString(cycle, item);
    this.relationType = relationType;
  }
  
  public CycleInRelationsError(SourceLocation loc, String itemType, ClusterChart item, Collection<String> cycle, String relationType) {
    super(loc);
    this.itemType = itemType;
    this.item = item.getName();
    this.cycleString = convertToCycleString(cycle, item.getName());
    this.relationType = relationType;
  }
  
  //For testing
  public CycleInRelationsError(SourceLocation loc, String itemType, String itemName, String cycle, String relationType) {
    super(loc);
    this.itemType = itemType;
    this.item = itemName;
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
  
  private static String convertToCycleString(Collection<ClassChart> cycle, ClassChart start) {
    StringBuilder sb = new StringBuilder();
    for (ClassChart chart : cycle) {
      sb.append(chart.getName().getName());
      sb.append("->");
    }
    sb.append(start.getName().getName());
    return sb.toString();
  }

  @Override
  public String getMessage() {
    if (cycleString == null) {
      return String.format(message1, itemType, item, relationType);
    } else {
      return String.format(message2, itemType, item, relationType, cycleString);
    }
  }
  
}
