
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;

public class Indexing extends AstNode {



  private final List<IndexClause> indexes;


  // === Constructors and Factories ===
  protected Indexing(List<IndexClause> indexes, SourceLocation location) {
    super(location);
    this.indexes = indexes; assert indexes != null;
    
  }
  
  public static Indexing mk(List<IndexClause> indexes, SourceLocation location) {
    return new Indexing(indexes, location);
  }

  // === Accessors ===

  public List<IndexClause> getIndexes() { return indexes; }

  // === Others ===
  @Override
  public Indexing clone() {
    List<IndexClause> newIndexes = indexes;
    
    return Indexing.mk(newIndexes, getLocation());
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("Indexing ast node: ");
    
    sb.append("indexes = ");
    sb.append(indexes);
    sb.append(", ");
    
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2,sb.length());
    }
    return sb.toString();
  }
}

