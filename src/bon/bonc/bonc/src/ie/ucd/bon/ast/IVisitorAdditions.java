package ie.ucd.bon.ast;

import ie.ucd.bon.source.SourceLocation;

public interface IVisitorAdditions {

  void visitCompactedIndirectionElement(CompactedIndirectionElement node, SourceLocation loc);
  
}
