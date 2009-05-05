/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2009 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package annot.attributes.clazz;

import java.util.Enumeration;
import java.util.Iterator;
import java.util.Vector;

import org.antlr.runtime.RecognitionException;

import annot.attributes.AttributeNames;
import annot.attributes.BCPrintableAttribute;
import annot.attributes.IBCAttribute;
import annot.bcclass.BCClass;
import annot.bcexpression.ExpressionRoot;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;

/**
 * This class represents Invariants class attribute described in "Invariants
 * Attribute" section of "BML Reference Manual".
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class InvariantsAttribute extends BCPrintableAttribute
                                 implements ClassAttribute, IBCAttribute {

  /**
   * The class in which the current invariant table is embedded.
   */
  private BCClass bcc;

  /**
   * The collection of all the invariants in this class.
   */
  private Vector < ClassInvariant > invariants;

  /**
   * Create the invariant table for the given class.
   *
   * @param abcc the class in which the invariant table lays.
   */
  public InvariantsAttribute(final BCClass abcc) {
    this.bcc = abcc;
    invariants = new Vector();
  }

  /**
   * Replaces this annotation with the one parsed from
   * given String.
   *
   * @param code - correct code of annotation
   *     to replace with.
   * @throws RecognitionException - if <code>code</code>
   *     is not correct annotation's code.
   */
  @Override
  public void parse(final String code) throws RecognitionException {
    parse(bcc, null, null, 0, code);
  }

  /**
   * This method prints all the invariants in this invariant table to
   * the resulting String. It uses the printing out method in the
   * invariants to do that.
   *
   * @param conf - see {@link BMLConfig}.
   * @return string representation of annotation.
   */
  @Override
  public String printCode1(final BMLConfig conf) {
    final StringBuffer buf = new StringBuffer();
    for (final Iterator i = invariants.iterator(); i.hasNext();) {
      final ClassInvariant inv = (ClassInvariant) i.next();
      if (buf.length() > 0) buf.append("\n");
      buf.append(inv.printCode1(conf));
    }
    return buf.toString();
  }

  /**
   * Removes the invariants table from the class it is assigned to.
   */
  public void remove() {
    bcc.removeInvariants();
  }

  /**
   * Replaces existing attribute of this type in given
   * BCClass with this attribute. At the same time this method should
   * change its container class to the given one.
   *
   * @param abcc - BCClass to place this attribute as it's
   *     class attribute.
   */

  public void replace(final BCClass abcc) {
    this.bcc = abcc;
    bcc.removeInvariants();
    bcc.setInvariants(this);
  }

  /**
   * Replaces this annotation with a given one, updating
   * necessary references in BCClass.
   *
   * @param pa - annotation to replace with.
   */
  public void replaceWith(final BCPrintableAttribute pa) {
    bcc.setInvariants((InvariantsAttribute) pa);
    bcc = null;
  }

  /**
   * @return a simple string representation of the current attribute,
   *     for use in debugger only.
   */
  @Override
  public String toString() {
    return "attribute table with " + invariants.size() + " elements";
  }

  /**
   * @return all expressions (not recursively) in this
   *     attribute, empty array in this case
   */
  @Override
  public ExpressionRoot[] getAllExpressions() {
    return new ExpressionRoot[0];
  }

  /**
   * The invariants ({@link ClassInvariant}) in this table
   * represented as an Enumeration.
   *
   * @return the enumeration with the invariants
   */
  public Enumeration elements() {
    return invariants.elements();
  }

  /**
   * @return the number of invariants in this invariant table
   */
  public int size() {
    return invariants.size();
  }

  /**
   * This method adds the given invariant at the end of the current
   * list of invariants.
   *
   * @param inv the invariant to add
   * @param pos the position (starting with 0) to add the invariant at
   */
  public void add(final ClassInvariant inv, final int pos) {
    if (pos < invariants.size()) {
      invariants.set(pos, inv);
    } else {
      invariants.add(inv);
    }
  }

  /**
   * This method removes the given invariant from the current list
   * of invariants.
   *
   * @param classInvariant the invariant to remove.
   */
  public void remove(final ClassInvariant classInvariant) {
    invariants.remove(classInvariant);
  }

  /**
   * @return index to the Utf8 constant with the name  of the invariant
   *   table attribute
   */
  public int getIndex() {
    return bcc.getCp().findConstant(AttributeNames.INVARIANTS_ATTR);
  }

  /**
   * @return the name of the invariant table attribute
   */
  public String getName() {
    return AttributeNames.INVARIANTS_ATTR;
  }

  /**
   * The Invariants attribute is saved using the format:
   *
   * Invariants_attribute {
   *   u2 attribute_name_index;
   *   u4 attribute_length;
   *   u2 invariants_count;
   *     {
   *        u2 access_flags;
   *        formula_info invariant;
   *     } invariants[invariants_count];
   *   }
   * described in "Invariants Attribute" section of "BML Reference Manual".
   * Note that the handling of the fields <code>attribute_name_index</code> and
   * <code>attribute_length</code> is done by the {@link Unknown} BCEL
   * class.
   *
   * @param aw the writer to write the attribute to
   */
  public void save(final AttributeWriter aw) {
    aw.writeShort(invariants.size());
    for (int i = 0; i < invariants.size(); i++) {
      final ClassInvariant inv = (ClassInvariant) invariants.get(i);
      inv.save(aw);
    }
  }

  /**
   * The Invariants attribute is loaded using the format:
   *
   * Invariants_attribute {
   *   u2 attribute_name_index;
   *   u4 attribute_length;
   *   u2 invariants_count;
   *     {
   *        u2 access_flags;
   *        formula_info invariant;
   *     } invariants[invariants_count];
   *   }
   * described in "Invariants Attribute" section of "BML Reference Manual".
   * Note that the fields <code>attribute_name_index</code> and
   * <code>attribute_length</code> are handled by the {@link Unknown} BCEL
   * class and are already read by the caller of the method.
   *
   * @param ar the reader to read the attribute data from
   * @throws ReadAttributeException in case the attribute has incorrect
   *   structure
   */
  public void load(final AttributeReader ar) throws ReadAttributeException {
    final int size = ar.readShort();
    invariants = new Vector < ClassInvariant > (size);
    for (int i = 0; i < size; i++) {
      final ClassInvariant inv = new ClassInvariant(bcc, ar);
      invariants.add(i, inv);
    }

  }

}
