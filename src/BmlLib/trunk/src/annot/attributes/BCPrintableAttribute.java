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
import annot.attributes.method.InCodeAttribute;
import annot.attributes.method.MethodSpecification;
import annot.bcclass.BCClass;
import annot.bcclass.BCMethod;
import annot.bcclass.MLog;
import annot.bcclass.MessageLog;
import annot.bcexpression.ExpressionRoot;
import annot.io.AttributeReader;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.Parsing;

/**
 * This class represents all maximal annotations that
 * can be placed in one place in class'es code.
 * WARNING: use only {@link ExpressionRoot} as imediate
 * subexpressions.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public abstract class BCPrintableAttribute implements IBCAttribute {

  /**
   * Result of last printCode1(conf) method call.
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
  public String getLast_code() {
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
    final ClassAttribute pa = bcc.getParser().parseAttribute(m, ih,
                                                                   minor, code);
    if (pa.getClass() == this.getClass()) {
      replaceWith(pa);
    } else {
      MLog.putMsg(MessageLog.LEVEL_PNOTICE,
                  "**** attribute's class changed ****");
      // XXX untested
      remove();
      if (m == null) {
        bcc.addAttribute(pa);
      } else {
        if (pa instanceof MethodSpecification) {
          m.setMspec((MethodSpecification) pa);
        } else if (pa instanceof InCodeAttribute) {
          m.addAttribute((InCodeAttribute) pa);
        } else {
          throw new RuntimeException("(BCPrintableAttribute.parse) Unknown " +
                                     "attribute");
        }
      }
    }
  }


  /**
   * Replaces the current annotation with a given one in the class
   * ({@link BCClass}) in which the current annotation resides. The method
   * updates necessary references in the {@link BCClass}.
   *
   * @param pa - annotation to replace with.
   */
  public abstract void replaceWith(ClassAttribute pa);

  /**
   * Replaces this annotation with the one parsed from
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
   * This method should simply print annotation to a string.
   *
   * @param conf - see {@link BMLConfig}.
   * @return string representation of annotation.
   */
  protected abstract String printCode1(BMLConfig conf);

  /**
   * Removes this annotation from its container (i.e. class in case
   * the annotation is a class annotation or method in case the annotation
   * is a class annotation).
   */
  public abstract void remove();

  /**
   * @return Simple string represenatations of attribute,
   *     for use in debugger only.
   */
  @Override
  public abstract String toString();

  /**
   * Loads this annotation from BCEL's Unknown attribute,
   * using attributeReader. It leaves the implementation to the subclasses.
   *
   * @param ar - stream to load from
   * @throws ReadAttributeException in case the BML
   *     attribute wasn't correctly parsed by this library.
   */
  public abstract void load(final AttributeReader ar)
    throws ReadAttributeException;

}
