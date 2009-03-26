/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker;

import ie.ucd.bon.ast.Type;

public class FeatureArgument {

  private final Type type;
  private final String name;
  
  public FeatureArgument(String name, Type type) {
    this.name = name;
    this.type = type;
  }

  public Type getType() {
    return type;
  }

  public String getName() {
    return name;
  } 
  
}
