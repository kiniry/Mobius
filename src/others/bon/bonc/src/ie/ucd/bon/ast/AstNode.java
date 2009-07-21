package ie.ucd.bon.ast;

import ie.ucd.bon.source.SourceLocation;

public abstract class AstNode {

  private final SourceLocation location;

  public AstNode(SourceLocation location) {
    this.location = location;
  }

  public SourceLocation getLocation() {
    return location;
  }
  
  public abstract void accept(IVisitor visitor);

}
