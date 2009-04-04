/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.informal;

import ie.ucd.bon.ast.Indexing;
import ie.ucd.bon.source.SourceLocation;

public class ClusterChartDefinition {

  private final String clusterName;
  private final SourceLocation loc;
  
  private boolean hasClusterHierarchyCycle;
  
  private Indexing indexing;
  
  private final boolean isSystem;
  
  public ClusterChartDefinition(String clusterName, SourceLocation loc, boolean isSystem) {
    this.clusterName = clusterName;
    this.loc = loc;    
    this.hasClusterHierarchyCycle = false;
    this.isSystem = isSystem;
  }

  public String getName() {
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

  public Indexing getIndexing() {
    return indexing;
  }

  public void setIndexing(Indexing indexing) {
    this.indexing = indexing;
  }

  public boolean isSystem() {
    return isSystem;
  }

  @Override
  public String toString() {
    return "ClusteChartDefinition: " + clusterName;
  }
  
  
  
}
