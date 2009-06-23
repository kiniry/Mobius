/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2009 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package annot.bcexpression;

import annot.bcexpression.formula.AbstractFormula;
import annot.bcexpression.javatype.JavaReferenceType;
import annot.bcexpression.javatype.JavaType;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;

/**
 * This class represents method's exception type (throws
 * declaration) with condition in which such exception
 * can be thrown by this method.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class Exsure {
  //XXX shouldn't I attached here reference to describing method?

  /**
   * Type of the exception declared.
   */
  private final JavaReferenceType excType;

  /**
   * Postcondition that is ensured in case of throwing
   * <code>excType</code> exception by this method.
   */
  private final ExpressionRoot < AbstractFormula >  postcondition;

  /**
   * A constructor from AttributeReader. Each exsures entry has the form
   * <pre>
   * {
   *    u2 exception_index;
   *    formula_info exsures_formula;
   * }
   * </pre>
   *
   * @param ar input stream to load from
   * @throws ReadAttributeException if remaining stream in
   *     <code>ar</code> does not represent a correct Exsure
   *     attribute
   */
  public Exsure(final AttributeReader ar) throws ReadAttributeException {
    final int cpindex = ar.readShort(); // read the exception index
    final String name = ar.findString(cpindex); //interpret from the const. pool
    final BCExpression expr = JavaType.getJavaType(name);
    if (!(expr instanceof JavaReferenceType)) {
      throw new ReadAttributeException("JavaType expected");
    }
    this.excType = (JavaReferenceType) expr;
    this.postcondition = new ExpressionRoot < AbstractFormula > (this, ar
        .readFormula()); // read the exsures formula
  }

  /**
   * A standard constructor.
   *
   * @param anexcType - exception type,
   * @param apostcondition - postcondition exsures when
   *     <code>excType</code> exception is thrown
   *     by this method.
   */
  public Exsure(final JavaReferenceType anexcType,
                final AbstractFormula apostcondition) {
    this.excType = anexcType;
    this.postcondition = new ExpressionRoot < AbstractFormula > (this,
                                                             apostcondition);
  }

  /**
   * @return Type of the exception declared.
   */
  public JavaReferenceType getExcType() {
    return this.excType;
  }

  /**
   * @return Postcondition that is ensured in case
   *     of throwing <code>excType</code> exception
   *     by this method.
   */
  public ExpressionRoot < AbstractFormula >  getPostcondition() {
    return this.postcondition;
  }

  /**
   * Displays this exsure to a String.
   *
   * @param conf - see {@link BMLConfig}.
   * @return String representation of this excondition.
   */
  public String printCode(final BMLConfig conf) {
    final String prefix = "(" + this.excType.printCode2(conf) + ")";
    return this.postcondition.printLine(conf, prefix);
  }

  /**
   * Writes this exsure to AttributeWriter. The format in which we write is:
   * <pre>
   * {
   *    u2 exception_index;
   *    formula_info exsures_formula;
   * }
   * </pre>
   *
   * @param aw - output stream to save to.
   */
  public void writeSingle(final AttributeWriter aw) {
    final int cpindex = aw.findConstant(this.excType.getSignature());
    aw.writeShort(cpindex);
    this.postcondition.write(aw);
  }

}
