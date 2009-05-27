
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;

public class ClusterChart extends InformalChart {


  private final Indexing indexing;

  private final String name;
  private final List<ClassEntry> classes;
  private final List<ClusterEntry> clusters;
  private final String explanation;
  private final String part;


  // === Constructors and Factories ===
  protected ClusterChart(String name, List<ClassEntry> classes, List<ClusterEntry> clusters, Indexing indexing, String explanation, String part, SourceLocation location) {
    super(location);
    this.name = name; assert name != null;
    this.classes = classes; assert classes != null;
    this.clusters = clusters; assert clusters != null;
    this.indexing = indexing; 
    this.explanation = explanation; 
    this.part = part; 
    
  }
  
  public static ClusterChart mk(String name, List<ClassEntry> classes, List<ClusterEntry> clusters, Indexing indexing, String explanation, String part, SourceLocation location) {
    return new ClusterChart(name, classes, clusters, indexing, explanation, part, location);
  }

  // === Accessors ===

  public String getName() { return name; }
  public List<ClassEntry> getClasses() { return classes; }
  public List<ClusterEntry> getClusters() { return clusters; }
  public Indexing getIndexing() { return indexing; }
  public String getExplanation() { return explanation; }
  public String getPart() { return part; }

  // === Visitor ===
  public void accept(IVisitor visitor) {
    visitor.visitClusterChart(this, name, classes, clusters, indexing, explanation, part, getLocation());
  }

  // === Others ===
  @Override
  public ClusterChart clone() {
    String newName = name;
    List<ClassEntry> newClasses = classes;
    List<ClusterEntry> newClusters = clusters;
    Indexing newIndexing = indexing == null ? null : indexing.clone();
    String newExplanation = explanation;
    String newPart = part;
    
    return ClusterChart.mk(newName, newClasses, newClusters, newIndexing, newExplanation, newPart, getLocation());
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("ClusterChart ast node: ");
    
    sb.append("name = ");
    sb.append(name);
    sb.append(", ");
    
    sb.append("classes = ");
    sb.append(classes);
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

