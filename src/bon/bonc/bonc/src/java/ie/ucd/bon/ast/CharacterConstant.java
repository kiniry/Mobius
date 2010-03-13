
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

public class CharacterConstant extends ManifestConstant {



  public final Character value;


  // === Constructors and Factories ===
  protected CharacterConstant(Character value, SourceLocation location) {
    super(location);
    this.value = value; assert value != null;
  }

  public static CharacterConstant mk(Character value, SourceLocation location) {
    return new CharacterConstant(value, location);
  }

  // === Accessors ===

  public Character getValue() { return value; }

  // === Visitor ===
  public void accept(IVisitorWithAdditions visitor) {
    visitor.visitCharacterConstant(this, value, getLocation());
  }

  // === Others ===
  @Override
  public CharacterConstant clone() {
    Character newValue = value;
    return CharacterConstant.mk(newValue, getLocation());
  }

  @Override
  public String toString() {
    return StringUtil.prettyPrint(this);
  }
}

