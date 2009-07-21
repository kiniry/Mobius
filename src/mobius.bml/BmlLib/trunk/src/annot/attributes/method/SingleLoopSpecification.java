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
import annot.bcexpression.BCExpression;
import annot.bcexpression.ExpressionRoot;
import annot.bcexpression.NumberLiteral;
import annot.bcexpression.formula.Predicate0Ar;
import annot.textio.BMLConfig;
import annot.textio.DisplayStyle;

/**
 * This class represents a single loop specification annotation.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class SingleLoopSpecification extends InCodeAnnotation {


  /**
   * The position of the invariant clause in the array of all expressions
   * returned by {@link #getAllExpressions()}.
   */
  public static final int INVARIANT_POS = 0;

  /**
   * The position of the variant clause in the array of all expressions
   * returned by {@link #getAllExpressions()}.
   */
  public static final int VARIANT_POS = 1;

  /**
   * An alias for the maximal position in the array of all expressions
   * returned by {@link #getAllExpressions()}.
   */
  private static final int MAX_POS = VARIANT_POS;

  /**
   * a loop variant.
   */
  private ExpressionRoot < BCExpression >  variant;

  /**
   * a loop's invariant.
   */
  private ExpressionRoot < BCExpression >  invariant;

  /**
   * A standard constructor.
   *
   * @param m - BCMethod containing this annotation,
   * @param ih - instructionHandle of bytecode instruction
   *     that this annotation should be attached to,
   * @param minor - minor number of annotation, responsible
   *     for annotation ordering within single instruction,
   * @param ainvariant - loop's invariant,
   * @param adecreases - loop's variant.
   */
  public SingleLoopSpecification(final BCMethod m, final InstructionHandle ih,
                                 final int minor,
                                 final BCExpression ainvariant,
                                 final BCExpression adecreases) {
    super(m, ih, minor);
    this.invariant = setNewExpression(ainvariant, new Predicate0Ar(true));
    this.variant = setNewExpression(adecreases, new NumberLiteral(1));
  }

  /**
   * Conditional method which returns the first argument in case it is non-null
   * and the second one otherwise. In each case the expression is packed
   * in an {@link ExpressionRoot} object.
   *
   * @param externalexpr the first candidate expression to return
   * @param dexpr the second candidate expression to return
   * @return the chosen expression packed in {@link ExpressionRoot}
   */
  private ExpressionRoot < BCExpression > setNewExpression(
      final BCExpression externalexpr, final BCExpression dexpr) {
    BCExpression expr = externalexpr;
    if (expr == null) {
      expr = dexpr;
    }
    return new ExpressionRoot < BCExpression > (this, expr);
  }


  /**
   * @return annotation's type id, from {@link AType} interface.
   */
  protected int aType() {
    return AType.C_LOOPSPEC;
  }

  /**
   * Returns all the expressions in this loop specification i.e.
   * its modifies clause (at {@link #MODIFIES_POS}), its invariant
   * (at {@link #INVARIANT_POS}), and its variant pattern (at
   * {@link #VARIANT_POS}).
   *
   * @return the expressions of this loop specification
   */
  @Override
  public ExpressionRoot[] getAllExpressions() {
    final ExpressionRoot[] all = new ExpressionRoot[MAX_POS + 1];
    all[INVARIANT_POS] = this.invariant;
    all[VARIANT_POS] = this.variant;
    return all;
  }

  /**
   * This method should simply print the annotation to a string.
   *
   * @param conf - see {@link BMLConfig}.
   * @return string representation of assertion.
   */
  @Override
  protected String printCode1(final BMLConfig conf) {
    String code = DisplayStyle.LOOPSPEC_KWD;
    conf.incInd();
    code += conf.nl() +
      this.invariant.printLine(conf, DisplayStyle.LOOP_INV_KWD);
    code += conf.nl() +
      this.variant.printLine(conf, DisplayStyle.DECREASES_KWD);
    conf.decInd();
    return code;
  }

  /**
   * @return simple string representation of the current annotation;
   *     for use in debugger only
   */
  @Override
  public String toString() {
    return "loop spec. at (" + getPC() + ", " +
      (getMinor() == -1 ? "any" : getMinor() + "") + ")";
  }

  /**
   * The loop invariant clause for the current loop specification case.
   *
   * @return the invariant clause for the current loop specification
   */
  public BCExpression getInvariant() {
    return invariant;
  }

  /**
   * The loop variant (decreases) clause for the current loop specification
   * case.
   *
   * @return the variant clause for the current loop specification
   */
  public BCExpression getVariant() {
    return variant;
  }

}
