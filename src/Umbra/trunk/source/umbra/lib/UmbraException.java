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
 * This is an exception used in tracing internal exceptional flows within
 * Umbra. This exception should not be handled outside Umbra.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 *
 */
public class UmbraException extends Exception {

  /**
   * The serial ID for the exception.
   */
  private static final long serialVersionUID = -8982650711998004110L;

  /**
   * The standard way to create the exception.
   */
  public UmbraException() {
  }

}
