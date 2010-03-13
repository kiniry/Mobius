
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

public class Type extends AstNode {



  public final String identifier;
  public final List<Type> actualGenerics;


  // === Constructors and Factories ===
  protected Type(String identifier, List<Type> actualGenerics, SourceLocation location) {
    super(location);
    this.identifier = identifier; assert identifier != null;
    this.actualGenerics = actualGenerics; assert actualGenerics != null;
  }

  public static Type mk(String identifier, List<Type> actualGenerics, SourceLocation location) {
    return new Type(identifier, actualGenerics, location);
  }

  // === Accessors ===

  public String getIdentifier() { return identifier; }
  public List<Type> getActualGenerics() { return actualGenerics; }

  // === Visitor ===
  public void accept(IVisitorWithAdditions visitor) {
    visitor.visitType(this, identifier, actualGenerics, getLocation());
  }

  // === Others ===
  @Override
  public Type clone() {
    String newIdentifier = identifier;
    List<Type> newActualGenerics = actualGenerics;
    return Type.mk(newIdentifier, newActualGenerics, getLocation());
  }

  @Override
  public String toString() {
    return StringUtil.prettyPrint(this);
  }
}

