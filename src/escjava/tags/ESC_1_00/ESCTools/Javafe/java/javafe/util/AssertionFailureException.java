/* Copyright 2000, 2001, Compaq Computer Corporation */


package javafe.util;

public class AssertionFailureException extends RuntimeException {
  AssertionFailureException() { }
  AssertionFailureException(String msg) { super(msg); }
}
