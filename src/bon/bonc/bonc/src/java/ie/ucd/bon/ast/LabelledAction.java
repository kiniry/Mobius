
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

public class LabelledAction extends AstNode {



  public final String label;
  public final String description;


  // === Constructors and Factories ===
  protected LabelledAction(String label, String description, SourceLocation location) {
    super(location);
    this.label = label; assert label != null;
    this.description = description; assert description != null;
  }

  public static LabelledAction mk(String label, String description, SourceLocation location) {
    return new LabelledAction(label, description, location);
  }

  // === Accessors ===

  public String getLabel() { return label; }
  public String getDescription() { return description; }

  // === Visitor ===
  public void accept(IVisitorWithAdditions visitor) {
    visitor.visitLabelledAction(this, label, description, getLocation());
  }

  // === Others ===
  @Override
  public LabelledAction clone() {
    String newLabel = label;
    String newDescription = description;
    return LabelledAction.mk(newLabel, newDescription, getLocation());
  }

  @Override
  public String toString() {
    return StringUtil.prettyPrint(this);
  }
}

