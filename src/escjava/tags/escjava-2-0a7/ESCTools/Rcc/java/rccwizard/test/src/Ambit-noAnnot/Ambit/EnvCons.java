// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Ambit;

public class EnvCons extends Env {

  private String ide;
  private Result val;
  private Env next;

  public EnvCons(String ide, Result val, Env next) {
    this.ide = ide;
    this.val = val;
    this.next = next;        
  }

  public Result fetch(String ide) throws AmbitException {
    if (ide.equals(this.ide)) { 
      return val;
    } else {
      return next.fetch(ide);
    }
  }
  
  public String toString() {
    return ide + "=" + val.toString() + "  " + next.toString();
  }

    
}
