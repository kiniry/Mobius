/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2009 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package annot.attributes.method;

import annot.attributes.AType;
import annot.attributes.AttributeNames;
import annot.bcclass.BCAttributeMap;
import annot.bcclass.BCMethod;
import annot.bcexpression.formula.AbstractFormula;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;

/**
 * This class represents "assert table" method attribute.
 * It is used only in saving to / loading from JavaClass.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class AssertTable extends BCAttributeTable {

  /**
   * A constructor.
   *
   * @param m - method containing this attribute,
   * @param parent - BCAttributeMap containing
   *     its attributes. This attribute can only
   *     save to / load atrtbutes from BCEL's Unknown
   *     attribute, it doesn't store them itself.
   * @see BCAttributeTable#BCAttributeTable(BCMethod, BCAttributeMap)
   */
  public AssertTable(final BCMethod m, final BCAttributeMap parent) {
    super(m, parent);
  }

  /**
   * @return the name of the current attribute to be used by the
   *   BCEL attribute representation ({@link org.apache.bcel.classfile.Unknown}
   *   class).
   */
  @Override
  public String getName() {
    return AttributeNames.ASSERT_TABLE_ATTR;
  }

  /**
   * Loads single assert from an {@link AttributeReader}.
   *
   * @param m - a method containing this attribute,
   * @param ar - a stream to load the assert from.
   * @return the single assert loaded from the given attribute reader
   * @throws ReadAttributeException - if data left
   *     in <code>ar</code> doesn't represent a correct
   *     assert.
   */
  @Override
  protected SingleAssert loadSingle(final BCMethod m, final AttributeReader ar)
    throws ReadAttributeException {
    final AbstractFormula f = ar.readFormula();
    final SingleAssert sa = new SingleAssert(m, null, -1, f);
    return sa;
  }

  /**
   * Saves a single assert to an {@link AttributeWriter}.
   *
   * @param icannot the annotation to write to the writer to
   * @param aw a stream to write the annotation to
   */
  @Override
  protected void saveSingle(final InCodeAnnotation icannot,
                            final AttributeWriter aw) {
    final SingleAssert sa = (SingleAssert) icannot;
    sa.getFormula().write(aw);
  }

  /**
   * @return attribute type of a single annotation.
   */
  @Override
  protected int singleType() {
    return AType.C_ASSERT;
  }
}
