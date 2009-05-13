/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2009 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package annot.attributes.method;

import org.antlr.runtime.RecognitionException;

import annot.attributes.BCPrintableAttribute;
import annot.bcclass.BCMethod;
import annot.textio.BMLConfig;

/**
 * This class represents BML method attribute.
 * Each subclass of this class should have at most one
 * instance for each BCMethod.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public abstract class MethodAttribute extends BCPrintableAttribute {

  /**
   * Replaces this annotation with the one parsed from the
   * given {@link String}.
   *
   * @param code - correct code of annotation to replace with.
   * @throws RecognitionException - if <code>code</code> is not correct
   *   code of an annotation
   */
  public abstract void parse(String code) throws RecognitionException;

  /**
   * This method prints annotation to a string.
   *
   * @param conf the configuration of the printing area, see {@link BMLConfig}
   * @return string representation of the current annotation
   */
  @Override
  protected abstract String printCode1(BMLConfig conf);

  /**
   * Replaces attribute of this type in given method with
   * this attribute.
   *
   * @param m - method to have it's attribute replaced.
   */
  public abstract void replace(BCMethod m);

  /**
   * @return a simple string representation of the current attribute,
   *    used for debugging purposes
   */
  @Override
  public abstract String toString();

}
