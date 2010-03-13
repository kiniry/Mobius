
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

public class FeatureName extends IndirectionFeaturePart {



  public final String name;


  // === Constructors and Factories ===
  protected FeatureName(String name, SourceLocation location) {
    super(location);
    this.name = name; assert name != null;
  }

  public static FeatureName mk(String name, SourceLocation location) {
    return new FeatureName(name, location);
  }

  // === Accessors ===

  public String getName() { return name; }

  // === Visitor ===
  public void accept(IVisitorWithAdditions visitor) {
    visitor.visitFeatureName(this, name, getLocation());
  }

  // === Others ===
  @Override
  public FeatureName clone() {
    String newName = name;
    return FeatureName.mk(newName, getLocation());
  }

  @Override
  public String toString() {
    return StringUtil.prettyPrint(this);
  }
}

