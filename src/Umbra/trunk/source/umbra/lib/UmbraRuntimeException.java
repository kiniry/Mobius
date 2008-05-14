/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.lib;

/**
 * This is an exception used in reporting runtime exceptional events within
 * Umbra. This exception should not be handled either inside or outside Umbra.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 *
 */
public class UmbraRuntimeException extends RuntimeException {

  /**
   * The serial ID for the exception.
   */
  private static final long serialVersionUID = 4428245399391845887L;

  /**
   * Constructs a new Umbra runtime exception with the specified detail message.
   *
   * @param a_string the message of the exception
   */
  public UmbraRuntimeException(final String a_string) {
    super(a_string);
  }
}
