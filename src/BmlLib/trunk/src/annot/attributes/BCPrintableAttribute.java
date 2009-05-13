/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2009 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package annot.attributes;

import org.antlr.runtime.RecognitionException;
import org.apache.bcel.generic.InstructionHandle;

import annot.attributes.clazz.ClassAttribute;
import annot.attributes.method.InCodeAnnotation;
import annot.attributes.method.MethodSpecificationAttribute;
import annot.bcclass.BCClass;
import annot.bcclass.BCMethod;
import annot.bcclass.MLog;
import annot.bcclass.MessageLog;
import annot.bcexpression.ExpressionRoot;
import annot.textio.BMLConfig;
import annot.textio.Parsing;

/**
 * This class represents the methods which are used for parsing and printing
 * of an attribute.
 * WARNING: use only {@link ExpressionRoot} as imediate
 * subexpressions.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public abstract class BCPrintableAttribute {

  /**
   * Result of the last execution of {@link #printCode(BMLConfig) method call.
   */
  private String last_code = "";

  /**
   * @return all expressions (not recursively) in this
   *     attribute.
   */
  public abstract ExpressionRoot[] getAllExpressions();

  /**
   * @return String representation of this annotation
   *     in last printCode(conf) call.
   */
  public String getLastCode() {
    return this.last_code;
  }

  /**
   * Replaces this annotation with the one parsed from
   * given String.
   *
   * @param bcc - BCClass containing (even indirectly)
   *     currently this annotation,
   * @param m - BCMethod containing this annotation, if any,
   * @param ih - instruction that this anotation
   *     is attached to, if any,
   * @param minor - minor number of this annotation, if any,
   * @param code - new code to be parsed.
   * @throws RecognitionException - if <code>code</code>
   *     is not correct annotation's code.
   */
  protected void parse(final BCClass bcc, final BCMethod m,
                       final InstructionHandle ih, final int minor,
                       final String code) throws RecognitionException {
    final BCPrintableAttribute pa = bcc.getParser().parseAttribute(m, ih,
                                                                   minor, code);
    if (pa.getClass() == this.getClass()) {
      replaceWith(pa);
    } else {
      MLog.putMsg(MessageLog.LEVEL_PNOTICE,
                  "**** attribute's class changed ****");
      // XXX untested
      remove();
      if (m == null) {
        bcc.addAttribute((ClassAttribute)pa);
      } else {
        if (pa instanceof MethodSpecificationAttribute) {
          m.setMspec((MethodSpecificationAttribute) pa);
        } else if (pa instanceof InCodeAnnotation) {
          m.addAttribute((InCodeAnnotation) pa);
        } else {
          throw new RuntimeException("(BCPrintableAttribute.parse) Unknown " +
                                     "attribute");
        }
      }
    }
  }

  /**
   * Replaces this annotation with the one parsed from the
   * given String.
   *
   * @param code - correct code of annotation
   *     to replace with.
   * @throws RecognitionException - if <code>code</code>
   *     is not correct annotation's code.
   */
  public abstract void parse(String code) throws RecognitionException;

  /**
   * Prints annotation's code using subclass' method
   * and given display environment and context and then
   * stores last result in <code>last_code</code> field.
   *
   * @param conf - see {@link BMLConfig}.
   * @return string representation of annotation.
   */
  public String printCode(final BMLConfig conf) {
    final String ret = printCode1(conf);
    this.last_code = printCode1(conf);
    this.last_code = Parsing.removeComment(this.last_code);
    return ret;
  }

  /**
   * This method prints annotation to a string.
   *
   * @param conf the configuration of the printing area, see {@link BMLConfig}
   * @return string representation of the current annotation
   */
  protected abstract String printCode1(BMLConfig conf);

  /**
   * @return a simple string representation of the current attribute,
   *    used for debugging purposes
   */
  @Override
  public abstract String toString();

  /**
   * Removes the current attribute from its container (i.e. class in case
   * the annotation is a class annotation or method in case the annotation
   * is a class annotation).
   */
  public abstract void remove();

  /**
   * Replaces the current attribute with a given one in the class
   * ({@link BCClass}) in which the current annotation resides. The method
   * updates necessary references in the {@link BCClass}. It should do
   * nothing if the attribute in the parameter is of a different class
   * than the current attribute.
   *
   * @param pa - annotation to replace with.
   */
  public abstract void replaceWith(BCPrintableAttribute pa);

}
