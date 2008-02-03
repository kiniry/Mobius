/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.editor.parsing;

/**
 * @author alx
 * @version a-01
 *
 */
public class UmbraLocationException extends Exception {

  /**
   * The serial number of the class.
   */
  private static final long serialVersionUID = 1368987676616348613L;

  /**
   *  This field contains the location which is considered to be wrong.
   */
  private final int my_wrong_location;

  public UmbraLocationException(final int a_line) {
    my_wrong_location = a_line;
  }

  public int getWrongLocation() {
    return my_wrong_location;
  }

}
