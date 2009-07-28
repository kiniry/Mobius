/* Copyright 2000, 2001, Compaq Computer Corporation */


package javafe.tc;

public class LookupException extends Exception { 

  public int reason;
  
  public static final int NOTFOUND = 0;
  public static final int AMBIGUOUS = 1;
  public static final int BADTYPECOMBO = 2;
  public static final int NOTACCESSIBLE = 3;

  public LookupException(int reason) {
    this.reason = reason;
  }
}
