/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2009 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package annot.attributes.clazz;

import org.antlr.runtime.RecognitionException;
import org.apache.bcel.Constants;

import annot.attributes.AttributeNames;
import annot.attributes.BCPrintableAttribute;
import annot.attributes.IBCAttribute;
import annot.bcclass.BCClass;
import annot.bcclass.BCClassRepresentation;
import annot.bcexpression.ExpressionRoot;
import annot.bcexpression.formula.AbstractFormula;
import annot.bcexpression.formula.Predicate0Ar;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.DisplayStyle;
import annot.textio.Parsing;

/**
 * This class represents class invariant attribute.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class ClassInvariant extends BCPrintableAttribute
                            implements IBCAttribute, ClassAttribute {

  /**
   * The flag which contains the access flags for the current class
   * invariant.
   */
  private int access_flags;

  /**
   * BCClass containing this attribute.
   */
  private final BCClass bcc;

  /**
   * The invariant formula.
   */
  private ExpressionRoot < AbstractFormula >  invariant;

  /**
   * A constructor from BCClass and AbstractFormula.
   *
   * @param abcc - BCClass containing this invariant,
   * @param ainv - a invariant formula.
   * @param instanceflag - <code>true</code> in case the invariant is an
   *   instance invariant
   */
  public ClassInvariant(final BCClass abcc, final AbstractFormula ainv,
                        final boolean instanceflag) {
    this.bcc = abcc;
    this.invariant = new ExpressionRoot < AbstractFormula > (this, ainv);
    commitInstanceFlag(instanceflag);
  }

  /**
   * A constructor from attributeReader, for use in class
   * loading only.
   *
   * @param bcc2 - BCClass containing this invariant,
   * @param ar - {@link AttributeReader} to load invariant from, it is
   *   in a position right after the length field of the attribute
   * @throws ReadAttributeException - if data left
   *     in <code>ar</code> doesn't represent correct
   *     class invariant.
   */
  public ClassInvariant(final BCClassRepresentation bcc2,
                        final AttributeReader ar)
    throws ReadAttributeException {
    this.bcc = (BCClass) bcc2;
    commitInstanceFlag((this.access_flags & Constants.ACC_STATIC) == 0);
    this.load(ar);
  }

  /**
   * Creates empty invariant (with formula 'true').
   *
   * @param abcc - BCClass containing this invariant.
   * @param instanceflag - <code>true</code> in case the invariant is an
   *   instance invariant
   */
  public ClassInvariant(final BCClass abcc, final boolean instanceflag) {
    this.bcc = abcc;
    this.invariant = new ExpressionRoot < AbstractFormula > (this,
        new Predicate0Ar(true));
    commitInstanceFlag(instanceflag);
  }

  /**
   * This method propagates the instance flag to the
   * access_flags field.
   * @param instanceflag <code>true</code> in case the invariant is an
   *   instance invariant
   */
  private void commitInstanceFlag(final boolean instanceflag) {
    if (!instanceflag) {
      this.access_flags = this.access_flags | Constants.ACC_STATIC;
    }
  }

  /**
   * @return the access flags for the current invariant
   */
  public int getAccessFlags() {
    return this.access_flags;
  }

  /**
   * This method returns an array with all the expressions in it. It is
   * always one expression in case of an invariant.
   *
   * @return an array of expressions
   */
  @Override
  public ExpressionRoot[] getAllExpressions() {
    final ExpressionRoot[] all = new ExpressionRoot[1];
    all[0] = this.invariant;
    return all;
  }

  /**
   * @return the index in the constant pool of the attribute name or -1
   *   in case the name is not in the constant pool
   */
  public int getIndex() {
    return this.bcc.getCp().findConstant(AttributeNames.INVARIANTS_ATTR);
  }

  /**
   * @return the invariant formula.
   */
  public AbstractFormula getInvariant() {
    return this.invariant.getExpression();
  }

  /**
   * @return Unknown (BCEL) attribute name.
   */
  public String getName() {
    return AttributeNames.INVARIANTS_ATTR;
  }

  /**
   * Return the information if the invariant is instance/static.
   *
   * @return <code>true</code> in case the invariant is an instance
   *   invariant, <code>false</code> otherwise
   */
  public boolean isInstance() {
    return (this.access_flags & Constants.ACC_STATIC) == 0;
  }

  /**
   * Replaces this annotation with the one parsed from
   * given String.
   *
   * @param code - correct code of class invariant
   *     to replace with.
   * @throws RecognitionException - if <code>code</code>
   *     is not correct class invariant's code.
   */
  @Override
  public void parse(final String code) throws RecognitionException {
    parse(this.bcc, null, null, -1, code);
  }

  /**
   * Prints the code of the annotation to a String.
   *
   * @param conf - see {@link BMLConfig}.
   * @return String representation of this invariant.
   */
  @Override
  public String printCode1(final BMLConfig conf) {
    final String header = isInstance() ? DisplayStyle.INVARIANT_KWD :
                                         (DisplayStyle.STATIC_KWD + " " +
                                          DisplayStyle.INVARIANT_KWD);
    final String code = this.invariant.printLine(conf, header);
    return "\n" + Parsing.addComment(code);
  }

  /**
  * Removes this annotation.
  */
  public void remove() {
    this.bcc.remove(this);
  }

  /**
   * Replaces existing class invariant in given
   * BCClass with this attribute.
   *
   * @param abcc - BCClass to place this attribute as it's
   *     class invariant.
   */
  public void replace(final BCClass abcc) {
    abcc.setInvariant(this);
  }

  /**
   * Replaces this annotation with a given one, updating
   * necessary references in BCClass.
   *
   * @param pa - annotation to replace with.
   */
  public void replaceWith(final BCPrintableAttribute pa) {
    this.bcc.setInvariant((ClassInvariant) pa);
  }


  /**
   * @return Simple string represenatations of attribute,
   *     for use in debugger only.
   */
  @Override
  public String toString() {
    if (isInstance()) {
      return "invariant";
    } else {
      return "static invariant";
    }
  }


  /**
   * A single invariant structure is saved using the format:
   *
   *     {
   *        u2 access_flags;
   *        formula_info invariant;
   *     }
   *
   * described in "Invariants Attribute" section of "BML Reference Manual".
   *
   * @param aw the writer to write the attribute to
   */
  public void save(final AttributeWriter aw) {
    aw.writeShort(this.access_flags);
    this.invariant.write(aw);
  }

  /**
   * A single invariant structure is loaded using the format:
   *
   *     {
   *        u2 access_flags;
   *        formula_info invariant;
   *     }
   *
   * described in "Invariants Attribute" section of "BML Reference Manual".
   *
   * @param ar the reader from which the structure is read
   * @throws ReadAttributeException in case the invariant structure is incorrect
   */
  public void load(final AttributeReader ar) throws ReadAttributeException {
    this.access_flags = ar.readShort();
    this.invariant = new ExpressionRoot < AbstractFormula > (this,
        ar.readFormula());
  }


}
