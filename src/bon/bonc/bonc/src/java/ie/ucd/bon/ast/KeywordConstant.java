
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

public class KeywordConstant extends Constant {
  public static enum Constant {
    RESULT, 
    VOID, 
    CURRENT
  }


  public final Constant constant;


  // === Constructors and Factories ===
  protected KeywordConstant(Constant constant, SourceLocation location) {
    super(location);
    this.constant = constant; 
  }

  public static KeywordConstant mk(Constant constant, SourceLocation location) {
    return new KeywordConstant(constant, location);
  }

  // === Accessors ===

  public Constant getConstant() { return constant; }

  // === Visitor ===
  public void accept(IVisitorWithAdditions visitor) {
    visitor.visitKeywordConstant(this, constant, getLocation());
  }

  // === Others ===
  @Override
  public KeywordConstant clone() {
    Constant newConstant = constant;
    return KeywordConstant.mk(newConstant, getLocation());
  }

  @Override
  public String toString() {
    return StringUtil.prettyPrint(this);
  }
}

