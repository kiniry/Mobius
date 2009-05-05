/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2009 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package annot.attributes.clazz;

import annot.bcclass.BCClass;

/**
 * This class represents BML class attributes.
 * Each subclass of this class should have at most one
 * instance for each BCClass.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public interface ClassAttribute {

  /**
   * Removes this annotation from the class it resides in.
   */
  void remove();

  /**
   * Replaces existing attribute of this type in given
   * BCClass with this attribute. At the same time this method should
   * change its container class to the given one.
   *
   * @param bcc - BCClass to place this attribute as it's
   *     class attribute.
   */
  void replace(BCClass bcc);

  /**
   * @return a simple string representation of the current attribute,
   *     for use in debugger only.
   */
  String toString();

}
