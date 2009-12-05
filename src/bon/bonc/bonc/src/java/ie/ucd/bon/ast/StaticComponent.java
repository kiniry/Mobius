
/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 *
 * This class is generated automatically from abstract_classes.tpl.
 * Do not edit.
 */
package ie.ucd.bon.ast;

import ie.ucd.bon.source.SourceLocation;

public abstract class StaticComponent extends AstNode {

  public StaticComponent(SourceLocation location) {
    super(location);
  }

  // a more specific return type
  @Override
  public abstract StaticComponent clone();
}
