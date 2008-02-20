/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker;

public class FeatureArgument {

  private final Type type;
  private final String name;
  
  public FeatureArgument(String name, Type type) {
    this.name = name;
    this.type = type;
  } 
  
  
}
