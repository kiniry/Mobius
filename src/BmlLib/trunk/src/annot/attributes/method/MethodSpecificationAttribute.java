/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2009 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package annot.attributes.method;

import java.util.Vector;

import org.antlr.runtime.RecognitionException;

import annot.attributes.AttributeNames;
import annot.attributes.BCPrintableAttribute;
import annot.attributes.IBCAttribute;
import annot.bcclass.BCMethod;
import annot.bcexpression.ExpressionRoot;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.Parsing;

/**
 * This class represents method specification attribute.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class MethodSpecificationAttribute extends MethodAttribute implements
    IBCAttribute {

  /**
   * Method this annotation specifies.
   */
  private final BCMethod method;

  /**
   * Each of this cases specifies method's behaviour
   * in some conditions (if their's precondition's are true).
   */
  private Vector < SpecificationCase >  specCases;

  /**
   * Creates an empty method specification,
   * which tells nothing.
   *
   * @param m - method this annotation specifies.
   */
  public MethodSpecificationAttribute(final BCMethod m) {
    this(m, new SpecificationCase[0]);
  }

  /**
   * A standard constructor.
   *
   * @param m - method this annotation specifies,
   * @param sc - and specification cases.
   */
  public MethodSpecificationAttribute(final BCMethod m,
                             final SpecificationCase[] sc) {
    this.method = m;
    this.specCases = new Vector < SpecificationCase > ();
    for (int i = 0; i  <  sc.length; i++) {
      this.specCases.add(sc[i]);
    }
  }

  /**
   * Adds a specificationCase to this specification.
   * Doesn't check semantical correctness
   * of methodSpecification.
   *
   * @param sc - specificationCase to be appended
   *     to <code>specCase</code> list of this
   *     method specification.
   */
  public void addCase(final SpecificationCase sc) {
    this.specCases.add(sc);
  }

  /**
   * Returns all the specification cases in this specification.
   *
   * @return method specification cases
   */
  public Vector < SpecificationCase > getSpecificationCases() {
    return this.specCases;
  }

  /**
   * A method which returns all the expressions of the method specification.
   * It is used in the visitor pattern.
   *
   * @return the array with all the expressions
   */
  @Override
  public ExpressionRoot[] getAllExpressions() {
    int n = 1;
    for (int i = 0; i  <  this.specCases.size(); i++) {
      n += this.specCases.get(i).getExprCount();
    }
    final ExpressionRoot[] all = new ExpressionRoot[n];
    int pos = 1;
    for (int i = 0; i  <  this.specCases.size(); i++) {
      final ExpressionRoot[] sce = this.specCases.get(i).getAllExpressions();
      for (int j = 0; j  <  sce.length; j++) {
        all[pos++] = sce[j];
      }
    }
    if (pos != n) {
      throw new RuntimeException(
        "Error in MethodSpecificationAttribute.getAllExpressions(): " +
        n + " != " + pos);
    }
    return all;
  }

  /**
   * @return nameIndex of BCEL's Unknown
   *     attribute it represents.
   */
  public int getIndex() {
    return this.method.getBcc().getCp().
      findConstant(AttributeNames.METHOD_SPECIFICATION_ATTR);
  }

  /**
   * @return Unknown (BCEL) attribute name.
   */
  public String getName() {
    return AttributeNames.METHOD_SPECIFICATION_ATTR;
  }

  /**
   * Replaces this annotation with the one parsed from
   * given String.
   *
   * @param code - correct code of method specification
   *     to replace with.
   * @throws RecognitionException - if <code>code</code>
   *     is not correct method specification.
   */
  @Override
  public void parse(final String code) throws RecognitionException {
    parse(this.method.getBcc(), this.method, null, -1, code);
  }

  /**
   * Prints annotation to a string.
   *
   * @param conf - see {@link BMLConfig}.
   * @return string representation of method specification.
   */
  @Override
  protected String printCode1(final BMLConfig conf) {
    String code = ""; //precondition.printLine(conf, IDisplayStyle._requires);
    if (this.specCases.size()  >  0) {
      for (int i = 0; i  <  this.specCases.size(); i++) {
        code += this.specCases.get(i).printCode(conf);
      }
    }
    return Parsing.addComment(code);
  }

  /**
   * Removes this specification container from the current method.
   */
  @Override
  public void remove() {
    this.method.setMspec(null);
  }

  /**
   * Sets the current specification as the specification in the given
   * method.
   *
   * @param m the method to assign the specification to
   */
  @Override
  public void replace(final BCMethod m) {
    m.setMspec(this);
  }

  /**
   * Replaces this annotation with a given one, updating
   * nessesery references in BCMethod.
   *
   * @param pa - annotation to replace with.
   */
  public void replaceWith(final BCPrintableAttribute pa) {
    this.method.setMspec((MethodSpecificationAttribute)pa);
  }

  /**
   * Saves method specification to BCEL's Unknown attribute.
   *
   * @param aw - stream to save to.
   */
  public void save(final AttributeWriter aw) {
    aw.writeAttributeCount(this.specCases.size());
    for (int i = 0; i  <  this.specCases.size(); i++) {
      this.specCases.get(i).write(aw);
    }
  }

  /**
   * A method to load specifications from an {@link AttributeReader}.
   *
   * @param ar - stream to load from.
   * @throws ReadAttributeException - if data left
   *     in <code>ar</code> doesn't represent correct
   *     method specification.
   */
  public void load(final AttributeReader ar)
    throws ReadAttributeException {
    final int length = ar.readShort();
    this.specCases = new Vector < SpecificationCase > ();
    for (int i = 0; i  <  length; i++) {
      final SpecificationCase sc = new SpecificationCase(method, ar);
      this.specCases.add(sc);
    }
  }
  /**
   * @return Simple string represenatations of attribute,
   *     for use in debugger only.
   */
  @Override
  public String toString() {
    return "method specification of " + this.method.toString();
  }

}
