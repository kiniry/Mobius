// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Ambit;

public abstract class Env {
/* An environment for code run by an agent. */

  public abstract Result fetch(String ide) throws AmbitException;
  
  public abstract String toString();
  
}
