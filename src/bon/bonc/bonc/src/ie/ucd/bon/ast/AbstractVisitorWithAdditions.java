package ie.ucd.bon.ast;

import ie.ucd.bon.source.SourceLocation;

public abstract class AbstractVisitorWithAdditions extends AbstractVisitor implements IVisitorAdditions {

  public void visitCompactedIndirectionElement(CompactedIndirectionElement node, SourceLocation loc) {
    //Do nothing
  }
  
}
