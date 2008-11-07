/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package bmllib.utils;

import annot.textio.Parsing;

/**
 * This class contains the code of the methods which are used to manipulate
 * file names and files.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public final class FileUtils {

  /**
   * The empty private constructor to prevent generation of instances.
   */
  private FileUtils() {
  }

  /**
   * A method to convert the universal path representation
   * ("/" separates the path segments) to the local operating
   * system specific one.
   *
   * @param fileName the path in the universal representation
   * @return the path in the local operating system representation
   */
  public static String toOsSpecificName(final String fileName) {
    final String filesep = System.getProperty("file.separator");
    return fileName.replaceAll("/", Parsing.escape(filesep));
  }

}
