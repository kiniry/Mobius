
/**
 * Copyright (c) 2007-2010, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 *
 * This class is generated automatically from normal_classes.tpl.
 * Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.util.StringUtil;

public class Indexing extends AstNode {



  public final List<IndexClause> indexes;


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

  // === Visitor ===
  public void accept(IVisitorWithAdditions visitor) {
    visitor.visitIndexing(this, indexes, getLocation());
  }

  // === Others ===
  @Override
  public Indexing clone() {
    List<IndexClause> newIndexes = indexes;
    return Indexing.mk(newIndexes, getLocation());
  }

  @Override
  public String toString() {
    return StringUtil.prettyPrint(this);
  }
}

