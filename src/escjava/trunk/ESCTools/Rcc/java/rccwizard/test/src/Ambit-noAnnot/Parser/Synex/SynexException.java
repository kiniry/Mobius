// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Parser.Synex;

public class SynexException extends Exception {

  private String msg;

  public SynexException(String msg) {
    this.msg = msg;
  }
  
  public String getMessage() {
    return msg;
  }
 
}
