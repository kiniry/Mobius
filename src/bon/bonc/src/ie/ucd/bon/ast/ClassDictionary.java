
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.ast.AstNode;

public class ClassDictionary extends SpecificationElement {


  private final Indexing indexing;

  private final String systemName;
  private final List<DictionaryEntry> entries;
  private final String explanation;
  private final String part;

  private final SourceLocation location;

  // === Constructors and Factories ===
  protected ClassDictionary(String systemName, List<DictionaryEntry> entries, Indexing indexing, String explanation, String part) {
    this(systemName,entries,indexing,explanation,part, null);    
  }

  protected ClassDictionary(String systemName, List<DictionaryEntry> entries, Indexing indexing, String explanation, String part, SourceLocation location) {
    
    assert location != null;
    this.location = location;
    this.systemName = systemName; assert systemName != null;
    this.entries = entries; 
    this.indexing = indexing; 
    this.explanation = explanation; 
    this.part = part; 
    
  }
  
  public static ClassDictionary mk(String systemName, List<DictionaryEntry> entries, Indexing indexing, String explanation, String part) {
    return new ClassDictionary(systemName, entries, indexing, explanation, part);
  }

  public static ClassDictionary mk(String systemName, List<DictionaryEntry> entries, Indexing indexing, String explanation, String part, SourceLocation location) {
    return new ClassDictionary(systemName, entries, indexing, explanation, part, location);
  }

  // === Accessors ===

  public String getSystemName() { return systemName; }
  public List<DictionaryEntry> getEntries() { return entries; }
  public Indexing getIndexing() { return indexing; }
  public String getExplanation() { return explanation; }
  public String getPart() { return part; }

  // === Others ===
  @Override
  public ClassDictionary clone() {
    String newSystemName = systemName;
    List<DictionaryEntry> newEntries = entries;
    Indexing newIndexing = indexing == null ? null : indexing.clone();
    String newExplanation = explanation;
    String newPart = part;
    
    return ClassDictionary.mk(newSystemName, newEntries, newIndexing, newExplanation, newPart, location);
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("ClassDictionary ast node: ");
    
    sb.append("systemName = ");
    sb.append(systemName);
    sb.append(", ");
    
    sb.append("entries = ");
    sb.append(entries);
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

