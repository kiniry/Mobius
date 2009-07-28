/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.util;

public class AssertionFailureException extends RuntimeException
{
  //@ modifies this.*;
  AssertionFailureException() { }

  //@ modifies this.*;
  AssertionFailureException(String msg) { super(msg); }
}
