// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Ambit;

public class AmbitException extends Exception {

  public AmbitException(String msg) {
    super("Ambit exception: " + msg);
  }

}
