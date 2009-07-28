// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Ambit;

public class EnvEmpty extends Env {

  public EnvEmpty() {
  }
  
  public Result fetch(String ide) throws AmbitException {  
    throw new AmbitException("Undefined: " + ide);
  }

  public String toString() {
    return "";
  }

}
