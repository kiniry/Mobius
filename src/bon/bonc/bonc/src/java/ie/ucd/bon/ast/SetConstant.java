
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

public class SetConstant extends ManifestConstant {



  public final List<EnumerationElement> enumerations;


  // === Constructors and Factories ===
  protected SetConstant(List<EnumerationElement> enumerations, SourceLocation location) {
    super(location);
    this.enumerations = enumerations; 
  }

  public static SetConstant mk(List<EnumerationElement> enumerations, SourceLocation location) {
    return new SetConstant(enumerations, location);
  }

  // === Accessors ===

  public List<EnumerationElement> getEnumerations() { return enumerations; }

  // === Visitor ===
  public void accept(IVisitorWithAdditions visitor) {
    visitor.visitSetConstant(this, enumerations, getLocation());
  }

  // === Others ===
  @Override
  public SetConstant clone() {
    List<EnumerationElement> newEnumerations = enumerations;
    return SetConstant.mk(newEnumerations, getLocation());
  }

  @Override
  public String toString() {
    return StringUtil.prettyPrint(this);
  }
}

