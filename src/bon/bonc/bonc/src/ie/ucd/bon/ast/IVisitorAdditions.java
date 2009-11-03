/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.ast;

import ie.ucd.bon.source.SourceLocation;

public interface IVisitorAdditions {

  void visitCompactedIndirectionElement(CompactedIndirectionElement node, SourceLocation loc);
  
}
