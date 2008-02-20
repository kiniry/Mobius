/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.informal;

import ie.ucd.bon.parser.SourceLocation;

public class ClusterChartDefinition {

  private final String clusterName;
  private final SourceLocation loc;
  
  private boolean hasClusterHierarchyCycle;
  
  public ClusterChartDefinition(String clusterName, SourceLocation loc) {
    this.clusterName = clusterName;
    this.loc = loc;    
    this.hasClusterHierarchyCycle = false;
  }

  public String getClusterName() {
    return clusterName;
  }

  public SourceLocation getSourceLocation() {
    return loc;
  }

  @Override
  public boolean equals(Object obj) {
    if (obj instanceof ClusterChartDefinition) {
      return clusterName.equals(((ClusterChartDefinition)obj).clusterName);
    } else {
      return false;
    }
  }

  @Override
  public int hashCode() {
    return clusterName.hashCode();
  }
  
  public void setHasClusterHierarchyCycle() {
    this.hasClusterHierarchyCycle = true;
  }
  
  public boolean hasClusterHierarchyCycle() {
    return hasClusterHierarchyCycle;
  }
  
}
