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
 * This is an exception used to trace situations when the synchronisation is
 * attempted for a line in the source code document not in the code
 * areas.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 *
 */
public class UmbraSynchronisationException extends Exception {

  /**
   * The serial ID for the exception.
   */
  private static final long serialVersionUID = 2772289259228267210L;

}
