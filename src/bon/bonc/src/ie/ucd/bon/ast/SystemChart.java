
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.ast.AstNode;

public class SystemChart extends InformalChart {


  private final Indexing indexing;

  private final String name;
  private final List<ClusterEntry> clusters;
  private final String explanation;
  private final String part;

  private final SourceLocation location;

  // === Constructors and Factories ===
  protected SystemChart(String name, List<ClusterEntry> clusters, Indexing indexing, String explanation, String part) {
    this(name,clusters,indexing,explanation,part, null);    
  }

  protected SystemChart(String name, List<ClusterEntry> clusters, Indexing indexing, String explanation, String part, SourceLocation location) {
    
    assert location != null;
    this.location = location;
    this.name = name; assert name != null;
    this.clusters = clusters; assert clusters != null;
    this.indexing = indexing; 
    this.explanation = explanation; 
    this.part = part; 
    
  }
  
  public static SystemChart mk(String name, List<ClusterEntry> clusters, Indexing indexing, String explanation, String part) {
    return new SystemChart(name, clusters, indexing, explanation, part);
  }

  public static SystemChart mk(String name, List<ClusterEntry> clusters, Indexing indexing, String explanation, String part, SourceLocation location) {
    return new SystemChart(name, clusters, indexing, explanation, part, location);
  }
  
  public SourceLocation getLocation() {
    return location;
  }

  // === Accessors ===

  public String getName() { return name; }
  public List<ClusterEntry> getClusters() { return clusters; }
  public Indexing getIndexing() { return indexing; }
  public String getExplanation() { return explanation; }
  public String getPart() { return part; }

  // === Others ===
  @Override
  public SystemChart clone() {
    String newName = name;
    List<ClusterEntry> newClusters = clusters;
    Indexing newIndexing = indexing == null ? null : indexing.clone();
    String newExplanation = explanation;
    String newPart = part;
    
    return SystemChart.mk(newName, newClusters, newIndexing, newExplanation, newPart, location);
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("SystemChart ast node: ");
    
    sb.append("name = ");
    sb.append(name);
    sb.append(", ");
    
    sb.append("clusters = ");
    sb.append(clusters);
    sb.append(", ");
    
    sb.append("indexing = ");
    sb.append(indexing);
    sb.append(", ");
    
    sb.append("explanation = ");
    sb.append(explanation);
    sb.append(", ");
    
    sb.append("part = ");
    sb.append(part);
    sb.append(", ");
    
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2,sb.length());
    }
    return sb.toString();
  }
}

