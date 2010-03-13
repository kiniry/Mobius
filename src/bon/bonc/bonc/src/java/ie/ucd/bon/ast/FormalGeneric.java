
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

public class FormalGeneric extends AstNode {


  public final Type type;

  public final String identifier;


  // === Constructors and Factories ===
  protected FormalGeneric(String identifier, Type type, SourceLocation location) {
    super(location);
    this.identifier = identifier; assert identifier != null;
    this.type = type; 
  }

  public static FormalGeneric mk(String identifier, Type type, SourceLocation location) {
    return new FormalGeneric(identifier, type, location);
  }

  // === Accessors ===

  public String getIdentifier() { return identifier; }
  public Type getType() { return type; }

  // === Visitor ===
  public void accept(IVisitorWithAdditions visitor) {
    visitor.visitFormalGeneric(this, identifier, type, getLocation());
  }

  // === Others ===
  @Override
  public FormalGeneric clone() {
    String newIdentifier = identifier;
    Type newType = type == null ? null : type.clone();
    return FormalGeneric.mk(newIdentifier, newType, getLocation());
  }

  @Override
  public String toString() {
    return StringUtil.prettyPrint(this);
  }
}

