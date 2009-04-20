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
import annot.attributes.clazz.ClassAttribute;
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
public abstract class MethodAttribute extends BCPrintableAttribute
                                      implements ClassAttribute {

  @Override
  public abstract void parse(String code) throws RecognitionException;

  @Override
  protected abstract String printCode1(BMLConfig conf);

  @Override
  public abstract void remove();

  /**
   * Replaces attribute of this type in given method with
   * this attribute.
   *
   * @param m - method to have it's attribute replaced.
   */
  public abstract void replace(BCMethod m);

  @Override
  public abstract String toString();

}
