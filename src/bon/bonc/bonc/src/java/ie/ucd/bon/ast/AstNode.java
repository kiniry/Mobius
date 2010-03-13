/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.ast;

import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.util.AstUtil;

public abstract class AstNode {

  public final SourceLocation location;

  public AstNode(SourceLocation location) {
    this.location = location;
  }

  public SourceLocation getLocation() {
    return location;
  }
  
  public SourceLocation getReportingLocation() {
    return AstUtil.getReportingSourceLocation(this);
  }

  public abstract void accept(IVisitorWithAdditions visitor);

}
