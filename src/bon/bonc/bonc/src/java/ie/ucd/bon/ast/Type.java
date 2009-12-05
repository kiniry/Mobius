
/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 *
 * This class is generated automatically from normal_classes.tpl.
 * Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;

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
    StringBuilder sb = new StringBuilder();
    sb.append("Type ast node: ");
    sb.append("identifier = ");
    sb.append(identifier);
    sb.append(", ");
        sb.append("actualGenerics = ");
    sb.append(actualGenerics);
    sb.append(", ");
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2, sb.length());
    }
    return sb.toString();
  }
}

