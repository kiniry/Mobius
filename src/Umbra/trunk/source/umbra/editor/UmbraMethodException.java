/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.editor;

/**
 * @author alx
 * @version a-01
 *
 */
public class UmbraMethodException extends Exception {

  /**
   * The serial number of the class.
   */
  private static final long serialVersionUID = 5973766671008411853L;

  /**
   *  This field contains the method number which is considered to be wrong.
   */
  private final int my_wrong_methodno;
  
  public UmbraMethodException(final int a_mno) {
    my_wrong_methodno = a_mno;
  }
  
  public int getWrongMethodNumber() {
    return my_wrong_methodno;
  }
}
