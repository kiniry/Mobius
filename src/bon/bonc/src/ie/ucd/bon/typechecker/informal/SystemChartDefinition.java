/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.informal;

import ie.ucd.bon.source.SourceLocation;

public class SystemChartDefinition {

  private final String systemName;
  private final SourceLocation loc;
  
  public SystemChartDefinition(String systemName, SourceLocation loc) {
    this.systemName = systemName;
    this.loc = loc;
  }

  public String getSystemName() {
    return systemName;
  }

  public SourceLocation getSourceLocation() {
    return loc;
  }   
  
}
