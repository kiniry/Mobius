
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.ast.AstNode;

public class IndexClause extends AstNode {



  private final String id;
  private final List<String> indexTerms;

private final SourceLocation location;

  // === Constructors and Factories ===
  protected IndexClause(String id, List<String> indexTerms) {
    this(id,indexTerms, null);    
  }

  protected IndexClause(String id, List<String> indexTerms, SourceLocation location) {
    
    assert location != null;
    this.location = location;
    this.id = id; assert id != null;
    this.indexTerms = indexTerms; assert indexTerms != null;
    
  }
  
  public static IndexClause mk(String id, List<String> indexTerms) {
    return new IndexClause(id, indexTerms);
  }

  public static IndexClause mk(String id, List<String> indexTerms, SourceLocation location) {
    return new IndexClause(id, indexTerms, location);
  }

  // === Accessors ===

  public String getId() { return id; }
  public List<String> getIndexTerms() { return indexTerms; }

  // === Others ===
  @Override
  public IndexClause clone() {
    String newId = id;
    List<String> newIndexTerms = indexTerms;
    
    return IndexClause.mk(newId, newIndexTerms, location);
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("IndexClause ast node: ");
    
    sb.append("id = ");
    sb.append(id);
    sb.append(", ");
    
    sb.append("indexTerms = ");
    sb.append(indexTerms);
    sb.append(", ");
    
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2,sb.length());
    }
    return sb.toString();
  }
}

