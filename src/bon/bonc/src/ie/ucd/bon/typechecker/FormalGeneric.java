/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker;

import ie.ucd.bon.parser.SourceLocation;

public class FormalGeneric {
  
  private final SourceLocation loc;
  private final String name;
  private final Type type;
  
  public FormalGeneric(String name, Type type, SourceLocation loc) {
    this.name = name;
    this.loc = loc;
    this.type = type;
  }
  
  
  
}
