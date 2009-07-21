/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2009 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package annot.attributes.method;

import java.util.Iterator;
import java.util.Vector;

import org.apache.bcel.classfile.ConstantUtf8;

import annot.bcclass.BCMethod;
import annot.bcexpression.ExpressionRoot;
import annot.bcexpression.Exsure;
import annot.bcexpression.formula.AbstractFormula;
import annot.bcexpression.formula.Predicate0Ar;
import annot.bcexpression.javatype.JavaReferenceType;
import annot.bcexpression.modifies.ModifyList;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.DisplayStyle;

/**
 * This class represents single specification case
 * of method specification.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class SpecificationCase {

  /**
   * A method this specificationCase specifies.
   */
  private final BCMethod method;

  /**
   * This expression describes what variables can change
   * in this case.
   */
  private ExpressionRoot < ModifyList >  modifies;

  /**
   * A condition that should be true if precondition is so.
   */
  private ExpressionRoot < AbstractFormula >  postcondition;

  /**
   * This case should be considered only if its precondition
   * evaluates to true.
   */
  private ExpressionRoot < AbstractFormula >  precondition;

  /**
   * The exception conditions vector. Each element contains a single
   * signals clause.
   */
  private Vector < Exsure >  excondition;

  /**
   * The vector with the exceptions declared in signals_only clause.
   */
  private Vector < JavaReferenceType >  signalsonly;

  /**
   * Creates an empty specification case, with both
   * precondition and postcondition set to true.
   *
   * @param m - a method this specificationCase specifies.
   */
  public SpecificationCase(final BCMethod m) {
    this.method = m;
    this.precondition = new ExpressionRoot < AbstractFormula > (
        this,
        new Predicate0Ar(true));
    this.modifies = new ExpressionRoot < ModifyList > (this, new ModifyList());
    this.postcondition = new ExpressionRoot < AbstractFormula > (
        this,
        new Predicate0Ar(true));
    createInitialExcondition();
    createInitialSignalsOnly(m);
  }

  /**
   * A constructor which generates the default signals and signals_only
   * cases.
   *
   * @param m - a method this specificationCase specifies.
   * @param aprecnd - a precondition of the specification case
   * @param amodifies - a modifies clause for the specification case
   * @param apostcondition - a postcondition for the specification case
   * @param anexsures - exceptional ensures for the specification case
   */
  public SpecificationCase(final BCMethod m,
                           final AbstractFormula aprecnd,
                           final ModifyList amodifies,
                           final AbstractFormula apostcondition,
                           final Vector < Exsure >  anexsures) {
    this.method = m;
    this.precondition = (aprecnd == null) ?
      new ExpressionRoot < AbstractFormula > (this, new Predicate0Ar(true)) :
      new ExpressionRoot < AbstractFormula > (this, aprecnd);
    final ModifyList mmod = (amodifies == null) ? new ModifyList() : amodifies;
    this.modifies = new ExpressionRoot < ModifyList > (this, mmod);
    final AbstractFormula mpostcondition = (apostcondition == null) ?
        new Predicate0Ar(true) : apostcondition;
    this.postcondition = new ExpressionRoot < AbstractFormula > (this,
                                                             mpostcondition);
    if (anexsures == null || anexsures.size() == 0) {
      createInitialExcondition();
    } else {
      this.excondition = anexsures;
    }
    createInitialSignalsOnly(m);
  }

  /**
   * A constructor which takes all the ingredients.
   *
   * @param m - a method this specificationCase specifies.
   * @param aprecnd - a precondition of the specification case
   * @param amodifies - a modifies clause for the specification case
   * @param apostcondition - a postcondition for the specification case
   * @param anexsures - exceptional ensures for the specification case
   * @param asonly - the signals_only exceptions
   */
  public SpecificationCase(final BCMethod m,
                           final AbstractFormula aprecnd,
                           final ModifyList amodifies,
                           final AbstractFormula apostcondition,
                           final Vector < Exsure >  anexsures,
                           final Vector < JavaReferenceType > asonly) {
    this.method = m;
    this.precondition = (aprecnd == null) ?
      new ExpressionRoot < AbstractFormula > (this, new Predicate0Ar(true)) :
      new ExpressionRoot < AbstractFormula > (this, aprecnd);
    final ModifyList mmod = (amodifies == null) ? new ModifyList() : amodifies;
    this.modifies = new ExpressionRoot < ModifyList > (this, mmod);
    final AbstractFormula mpostcondition = (apostcondition == null) ?
        new Predicate0Ar(true) : apostcondition;
    this.postcondition = new ExpressionRoot < AbstractFormula > (this,
                                                             mpostcondition);
    if (anexsures == null || anexsures.size() == 0) {
      createInitialExcondition();
    } else {
      this.excondition = anexsures;
    }
    if (asonly == null) {
      createInitialSignalsOnly(m);
    } else {
      this.signalsonly = asonly;
    }
  }

  /**
   * A constructor from AttributeReader, used only for
   * loading specification case from .class file.
   *
   * @param m - method this annotation specifies.
   * @param ar - stream to load from.
   * @throws ReadAttributeException - if data left
   *     in <code>ar</code> doesn't represent correct
   *     specification case.
   */
  public SpecificationCase(final BCMethod m, final AttributeReader ar)
    throws ReadAttributeException {
    this(m);
    this.precondition = new ExpressionRoot < AbstractFormula > (this, ar
        .readFormula());
    this.modifies = new ExpressionRoot < ModifyList > (this,
        new ModifyList(ar));
    this.postcondition = new ExpressionRoot < AbstractFormula > (this, ar
        .readFormula());
    this.excondition = new Vector < Exsure > ();
    final int count = ar.readItemsCount();
    for (int i = 0; i  <  count; i++) {
      final Exsure ex = new Exsure(ar);
      this.excondition.add(ex);
    }
    readInSignalsOnly(m, ar);
  }

  /**
   * The method reads from the given attribute reader stream the exceptions
   * from signals_only clause.
   *
   * @param m the method for which the signals_only is created
   * @param ar the reader to read the signals_only from
   * @throws ReadAttributeException if there is not enough
   *   bytes in the stream to read correctly the signals_only clause
   */
  private void readInSignalsOnly(final BCMethod m, final AttributeReader ar)
    throws ReadAttributeException {
    this.signalsonly = new Vector < JavaReferenceType > ();
    final int socount = ar.readItemsCount();
    for (int i = 0; i  <  socount; i++) {
      final int idx = ar.readShort();
      final String ename =
        ((ConstantUtf8)m.getBcc().getCp().getConstant(idx)).getBytes();
      final JavaReferenceType jrt = new JavaReferenceType(ename);
      this.signalsonly.add(jrt);
    }
  }


  /**
   * This method creates the initial signals condition:
   * signals (Exception) true.
   */
  private void createInitialExcondition() {
    this.excondition = new Vector < Exsure > ();
    this.excondition.add(
      new Exsure(new JavaReferenceType("java/lang/Exception"),
                 new Predicate0Ar(true)));
  }


  /**
   * Creates the initial value of the signals_only clause by
   * initialising it with the exceptions of the given method.
   *
   * @param ameth the method to extract the exceptions from
   */
  private void createInitialSignalsOnly(final BCMethod ameth) {
    final String [] exnames = ameth .getBcelMethod().getExceptions();
    this.signalsonly = new Vector < JavaReferenceType > ();
    for (int i = 0; i < exnames.length; i++) {
      this.signalsonly.add(new JavaReferenceType(exnames[i]));
    }
  }

  /**
   * @return Array of expressions (not recursivly) in this
   *     attribute (including expressions (postconditions)
   *     in excondition).
   */
  public ExpressionRoot[] getAllExpressions() {
    final int n = getExprCount();
    final ExpressionRoot[] all = new ExpressionRoot[n];
    int pos = 0;
    if (this.precondition != null) {
      all[pos++] = this.precondition;
    }
    if (this.modifies != null) {
      all[pos++] = this.modifies;
    }
    if (this.postcondition != null) {
      all[pos++] = this.postcondition;
    }
    if (this.excondition != null) {
      for (int i = 0; i  <  this.excondition.size(); i++) {
        all[pos++] = this.excondition.get(i).getPostcondition();
      }
    }
    return all;
  }

  /**
   * @return number of expressions (not recursivly) in this
   *     attribute (including expressions (postconditions)
   *     in excondition).
   */
  public int getExprCount() {
    int n = 0;
    if (this.precondition != null) {
      n++;
    }
    if (this.modifies != null) {
      n++;
    }
    if (this.postcondition != null) {
      n++;
    }
    if (this.excondition != null) {
      n += this.excondition.size();
    }
    return n;
  }

  /**
   * @return method this specificationCase specifies.
   */
  public BCMethod getMethod() {
    return this.method;
  }

  /**
   * Prints specification case to a string.
   *
   * @param conf - see {@link BMLConfig}.
   * @return string representation of specificatoin case.
   */
  public String printCode(final BMLConfig conf) {
    final StringBuffer code = new StringBuffer("");
    //code += IDisplayStyle._sc_start + conf.newLine();
    //conf.incInd();
    code.append(this.precondition.printLine(conf, DisplayStyle.REQUIRES_KWD));
    if (!this.modifies.getExpression().isEmpty()) {
      code.append(this.modifies.printLine(conf, DisplayStyle.MODIFIES_KWD));
    }
    code.append(this.postcondition.printLine(conf, DisplayStyle.ENSURES_KWD));
    printSignals(conf, code);
    printSignalsOnly(conf, code);
    //conf.decInd();
    //code += " " + IDisplayStyle._sc_end + conf.newLine();
    return code.toString();
  }

  /**
   * The method appends to the given {@link StringBuffer} the textual
   * representation of the signals_only clause.
   *
   * @param conf - see {@link BMLConfig}.
   * @param code the buffer to append the signals_only clause to
   */
  private void printSignalsOnly(final BMLConfig conf,
                                final StringBuffer code) {
    code.append(conf.getIndent()).append(DisplayStyle.SIGNALS_ONLY_KWD);
    if (this.signalsonly.size() == 0) {
      code.append(" ").append(DisplayStyle.NOTHING_KWD);
    } else {
      final Iterator < JavaReferenceType >  iter = this.signalsonly.iterator();
      code.append(" ").append(iter.next().getSignature());
      while (iter.hasNext()) {
        code.append(", ");
        code.append(iter.next().getSignature());
      }
    }
  }

  /**
   * The method appends to the given {@link StringBuffer} the textual
   * representation of the signals clause.
   *
   * @param conf - see {@link BMLConfig}.
   * @param code the buffer to append the signals clause to
   */
  private void printSignals(final BMLConfig conf,
                            final StringBuffer code) {
    if (this.excondition.size() == 1) {
      code.append(conf.getIndent()).append(DisplayStyle.SIGNALS_KWD).
           append(" ").append(this.excondition.get(0).printCode(conf));
    } else if (this.excondition.size()  >  1) {
      code.append(conf.getIndent()).append(DisplayStyle.SIGNALS_KWD);
      final Iterator < Exsure >  iter = this.excondition.iterator();
      while (iter.hasNext()) {
        code.append(conf.newLine());
        code.append(iter.next().printCode(conf));
      }
      conf.decInd();
      code.append(conf.newLine());
      conf.incInd();
    }
  }

  /**
   * Saves specification case using AttributeWriter.
   *
   * @param aw - stream to save to.
   */
  public void write(final AttributeWriter aw) {
    this.precondition.write(aw);
    this.modifies.write(aw);
    this.postcondition.write(aw);
    aw.writeAttributeCount(this.excondition.size());
    final Iterator < Exsure >  iter = this.excondition.iterator();
    while (iter.hasNext()) {
      iter.next().writeSingle(aw);
    }
    aw.writeAttributeCount(this.signalsonly.size());
    final Iterator < JavaReferenceType >  itera = this.signalsonly.iterator();
    while (itera.hasNext()) {
      final JavaReferenceType tp = itera.next();
      final String sig = tp.getSignature().replace('.', '/');
      final int idx = method.getBcc().getCp().getCoombinedCP().lookupUtf8(sig);
      aw.writeShort(idx);
    }
  }

  /**
   * @return the exceptional return conditions for the method
   */
  public Vector < Exsure > getExcondition() {
    return excondition;
  }

  /**
   * @return the modifies clause of the method
   */
  public ExpressionRoot < ModifyList > getModifies() {
    return modifies;
  }

  /**
   * @return the normal return postcondition of the method
   */
  public ExpressionRoot < AbstractFormula > getPostcondition() {
    return postcondition;
  }

  /**
   * @return the precondition of the method
   */
  public ExpressionRoot < AbstractFormula > getPrecondition() {
    return precondition;
  }
}
