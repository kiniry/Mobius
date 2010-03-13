
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

public class InheritanceRelation extends StaticRelation {


  public final StaticRef child;
  public final StaticRef parent;
  public final Multiplicity multiplicity;

  public final String semanticLabel;


  // === Constructors and Factories ===
  protected InheritanceRelation(StaticRef child, StaticRef parent, Multiplicity multiplicity, String semanticLabel, SourceLocation location) {
    super(location);
    this.child = child; assert child != null;
    this.parent = parent; assert parent != null;
    this.multiplicity = multiplicity; 
    this.semanticLabel = semanticLabel; 
  }

  public static InheritanceRelation mk(StaticRef child, StaticRef parent, Multiplicity multiplicity, String semanticLabel, SourceLocation location) {
    return new InheritanceRelation(child, parent, multiplicity, semanticLabel, location);
  }

  // === Accessors ===

  public StaticRef getChild() { return child; }
  public StaticRef getParent() { return parent; }
  public Multiplicity getMultiplicity() { return multiplicity; }
  public String getSemanticLabel() { return semanticLabel; }

  // === Visitor ===
  public void accept(IVisitorWithAdditions visitor) {
    visitor.visitInheritanceRelation(this, child, parent, multiplicity, semanticLabel, getLocation());
  }

  // === Others ===
  @Override
  public InheritanceRelation clone() {
    StaticRef newChild = child == null ? null : child.clone();
    StaticRef newParent = parent == null ? null : parent.clone();
    Multiplicity newMultiplicity = multiplicity == null ? null : multiplicity.clone();
    String newSemanticLabel = semanticLabel;
    return InheritanceRelation.mk(newChild, newParent, newMultiplicity, newSemanticLabel, getLocation());
  }

  @Override
  public String toString() {
    return StringUtil.prettyPrint(this);
  }
}

