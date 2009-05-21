
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;

public class DictionaryEntry extends AstNode {



  private final String name;
  private final List<String> clusters;
  private final String description;


  // === Constructors and Factories ===
  protected DictionaryEntry(String name, List<String> clusters, String description, SourceLocation location) {
    super(location);
    this.name = name; assert name != null;
    this.clusters = clusters; assert clusters != null;
    this.description = description; assert description != null;
    
  }
  
  public static DictionaryEntry mk(String name, List<String> clusters, String description, SourceLocation location) {
    return new DictionaryEntry(name, clusters, description, location);
  }

  // === Accessors ===

  public String getName() { return name; }
  public List<String> getClusters() { return clusters; }
  public String getDescription() { return description; }

  // === Others ===
  @Override
  public DictionaryEntry clone() {
    String newName = name;
    List<String> newClusters = clusters;
    String newDescription = description;
    
    return DictionaryEntry.mk(newName, newClusters, newDescription, getLocation());
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("DictionaryEntry ast node: ");
    
    sb.append("name = ");
    sb.append(name);
    sb.append(", ");
    
    sb.append("clusters = ");
    sb.append(clusters);
    sb.append(", ");
    
    sb.append("description = ");
    sb.append(description);
    sb.append(", ");
    
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2,sb.length());
    }
    return sb.toString();
  }
}

