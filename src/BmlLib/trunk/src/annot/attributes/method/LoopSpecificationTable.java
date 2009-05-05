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
import annot.attributes.BCAttributeTable;
import annot.attributes.IBCAttribute;
import annot.bcclass.BCMethod;
import annot.bcexpression.BCExpression;
import annot.bcexpression.formula.AbstractFormula;
import annot.bcexpression.modifies.ModifyList;
import annot.io.AttributeReader;
import annot.io.ReadAttributeException;

/**
 * This class represents "loop specification table" method
 * attribute. It is used only in saving to / loading from
 * JavaClass.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class LoopSpecificationTable extends BCAttributeTable {

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
  public LoopSpecificationTable(final BCMethod m, final BCAttributeMap parent) {
    super(m, parent);
  }

  @Override
  public String getName() {
    return AttributeNames.LOOP_SPECIFICATION_TABLE_ATTR;
  }

  @Override
  protected InCodeAttribute loadSingle(final BCMethod m,
                                       final AttributeReader ar)
    throws ReadAttributeException {
    final ModifyList modifies = new ModifyList(ar);
    final AbstractFormula invariant = ar.readFormula();
    final BCExpression decreases = ar.readExpression();
    return new SingleLoopSpecification(m, null, -1, modifies, invariant,
                                       decreases);
  }

  @Override
  protected int singleType() {
    return AType.C_LOOPSPEC;
  }

  /**
   * Removes this annotation from its container (i.e. class in case
   * the annotation is a class annotation or method in case the annotation
   * is a class annotation).
   */
  public void remove() {
    // TODO 
  }

  public void replaceWith(final IBCAttribute pa) {
    // TODO Auto-generated method stub
    
  }
}
