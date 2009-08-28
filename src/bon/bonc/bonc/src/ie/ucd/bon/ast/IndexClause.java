
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;

public class IndexClause extends AstNode {



  public final String id;
  public final List<String> indexTerms;


  // === Constructors and Factories ===
  protected IndexClause(String id, List<String> indexTerms, SourceLocation location) {
    super(location);
    this.id = id; assert id != null;
    this.indexTerms = indexTerms; assert indexTerms != null;
    
  }
  
  public static IndexClause mk(String id, List<String> indexTerms, SourceLocation location) {
    return new IndexClause(id, indexTerms, location);
  }

  // === Accessors ===

  public String getId() { return id; }
  public List<String> getIndexTerms() { return indexTerms; }

  // === Visitor ===
  public void accept(IVisitorWithAdditions visitor) {
    visitor.visitIndexClause(this, id, indexTerms, getLocation());
  }

  // === Others ===
  @Override
  public IndexClause clone() {
    String newId = id;
    List<String> newIndexTerms = indexTerms;
    
    return IndexClause.mk(newId, newIndexTerms, getLocation());
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

