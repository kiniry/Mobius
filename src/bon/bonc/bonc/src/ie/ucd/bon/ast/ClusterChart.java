
/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 *
 * This class is generated automatically from normal_classes.tpl.
 * Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;

public class ClusterChart extends InformalChart {


  public final Indexing indexing;

  public final String name;
  public final Boolean isSystem;
  public final List<ClassEntry> classes;
  public final List<ClusterEntry> clusters;
  public final String explanation;
  public final String part;


  // === Constructors and Factories ===
  protected ClusterChart(String name, Boolean isSystem, List<ClassEntry> classes, List<ClusterEntry> clusters, Indexing indexing, String explanation, String part, SourceLocation location) {
    super(location);
    this.name = name; assert name != null;
    this.isSystem = isSystem; assert isSystem != null;
    this.classes = classes; assert classes != null;
    this.clusters = clusters; assert clusters != null;
    this.indexing = indexing; 
    this.explanation = explanation; 
    this.part = part; 
  }

  public static ClusterChart mk(String name, Boolean isSystem, List<ClassEntry> classes, List<ClusterEntry> clusters, Indexing indexing, String explanation, String part, SourceLocation location) {
    return new ClusterChart(name, isSystem, classes, clusters, indexing, explanation, part, location);
  }

  // === Accessors ===

  public String getName() { return name; }
  public Boolean getIsSystem() { return isSystem; }
  public List<ClassEntry> getClasses() { return classes; }
  public List<ClusterEntry> getClusters() { return clusters; }
  public Indexing getIndexing() { return indexing; }
  public String getExplanation() { return explanation; }
  public String getPart() { return part; }

  // === Visitor ===
  public void accept(IVisitorWithAdditions visitor) {
    visitor.visitClusterChart(this, name, isSystem, classes, clusters, indexing, explanation, part, getLocation());
  }

  // === Others ===
  @Override
  public ClusterChart clone() {
    String newName = name;
    Boolean newIsSystem = isSystem;
    List<ClassEntry> newClasses = classes;
    List<ClusterEntry> newClusters = clusters;
    Indexing newIndexing = indexing == null ? null : indexing.clone();
    String newExplanation = explanation;
    String newPart = part;
    return ClusterChart.mk(newName, newIsSystem, newClasses, newClusters, newIndexing, newExplanation, newPart, getLocation());
  }

  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("ClusterChart ast node: ");
    sb.append("name = ");
    sb.append(name);
    sb.append(", ");
        sb.append("isSystem = ");
    sb.append(isSystem);
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
      sb.delete(sb.length()-2, sb.length());
    }
    return sb.toString();
  }
}

