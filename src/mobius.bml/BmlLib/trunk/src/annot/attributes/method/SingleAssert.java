/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2009 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package annot.attributes.method;

import org.apache.bcel.generic.InstructionHandle;

import annot.attributes.AType;
import annot.bcclass.BCMethod;
import annot.bcexpression.ExpressionRoot;
import annot.bcexpression.formula.AbstractFormula;
import annot.bcexpression.formula.Predicate0Ar;
import annot.textio.BMLConfig;
import annot.textio.DisplayStyle;

/**
 * This class represents single assert annotation
 * (on or more InCodeAnnotation per one bytecode instruction).
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class SingleAssert extends InCodeAnnotation {

  /**
   * The formula inside the current assert attribute.
   */
  private ExpressionRoot < AbstractFormula >  formula;

  /**
   * Creates an empty annotation: '/assert true'.
   *
   * @param m - BCMethod containing this annotation,
   * @param ih - instructionHandle of bytecode instruction
   *     that this annotation should be attached to,
   * @param minor - minor number of annotation, responsible
   *     for annotation ordering within single instruction.
   */
  public SingleAssert(final BCMethod m, final InstructionHandle ih,
                      final int minor) {
    super(m, ih, minor);
    this.formula = new ExpressionRoot < AbstractFormula > (this,
                                                       new Predicate0Ar(true));
  }

  /**
   * A standard constructor.
   *
   * @param m - BCMethod containing this annotation,
   * @param ih - instructionHandle of bytecode instruction
   *     that this annotation should be attached to,
   * @param minor - minor number of annotation, responsible
   *     for annotation ordering within single instruction.
   * @param aformula the formula inside the assert
   */
  public SingleAssert(final BCMethod m, final InstructionHandle ih,
                      final int minor,
                      final AbstractFormula aformula) {
    super(m, ih, minor);
    this.formula = new ExpressionRoot < AbstractFormula > (this, aformula);
  }

  /**
   * A constructor for tests only. It can be used only
   * when we are sure that bytecode itself won't change.
   * Creates an empty assert (/assert true).
   *
   * @param m - BCMethod containing this annotation,
   * @param pc - pc number of bytecode instruction that
   *     this annotation should be attached to. You should
   *     be sure that instruction of that pc really
   *     exists in given method.
   * @param minor - minor number of annotation, responsible
   *     for annotation ordering within single instruction.
   */
  @Deprecated
  public SingleAssert(final BCMethod m, final int pc, final int minor) {
    super(m, pc, minor);
    this.formula = new ExpressionRoot < AbstractFormula > (this,
                                                       new Predicate0Ar(true));
  }

  /**
   * A constructor for tests only. It can be used only
   * when we are sure that bytecode itself won't change.
   *
   * @param m - BCMethod containing this annotation,
   * @param pc - pc number of bytecode instruction that
   *     this annotation should be attached to. You should
   *     be sure that instruction of that pc really
   *     exists in given method.
   * @param minor - minor number of annotation, responsible
   *     for annotation ordering within single instruction.
   * @param f - assertion formula.
   */
  @Deprecated
  public SingleAssert(final BCMethod m, final int pc, final int minor,
                      final AbstractFormula f) {
    super(m, pc, minor);
    this.formula = new ExpressionRoot < AbstractFormula > (this, f);
  }

  /**
   * @return annotation's type id, from {@link AType} interface.
   */
  @Override
  protected int aType() {
    return AType.C_ASSERT;
  }

  /**
   * @return the only expression of this assert
   */
  @Override
  public ExpressionRoot[] getAllExpressions() {
    final ExpressionRoot[] all = new ExpressionRoot[1];
    all[0] = this.formula;
    return all;
  }

  /**
   * @return assertion formula.
   */
  public AbstractFormula getFormula() {
    return this.formula.getExpression();
  }

  /**
   * This method should simply print annotation to a string.
   *
   * @param conf - see {@link BMLConfig}.
   * @return string representation of assertion.
   */
  @Override
  protected String printCode1(final BMLConfig conf) {
    return this.formula.printLine(conf, DisplayStyle.ASSERT_KWD);
  }

  /**
   * @return simple string representation of the current annotation;
   *     for use in debugger only
   */
  @Override
  public String toString() {
    return "assert at (" + getPC() + ", " +
      (getMinor() == -1 ? "any" : "" + getMinor()) + ")";
  }

}
