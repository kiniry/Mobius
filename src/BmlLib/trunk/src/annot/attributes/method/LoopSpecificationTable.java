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
import annot.bcexpression.BCExpression;
import annot.bcexpression.formula.AbstractFormula;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
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
   *     save to / load attributes from BCEL's Unknown
   *     attribute, it doesn't store them itself.
   * @see BCAttributeTable#BCAttributeTable(BCMethod, BCAttributeMap)
   */
  public LoopSpecificationTable(final BCMethod m, final BCAttributeMap parent) {
    super(m, parent);
  }

  /**
   * @return the name of the current attribute to be used by the
   *   BCEL attribute representation ({@link org.apache.bcel.classfile.Unknown}
   *   class).
   */
  @Override
  public String getName() {
    return AttributeNames.LOOP_SPECIFICATION_TABLE_ATTR;
  }

  /**
   * Loads a single loop specification from an {@link AttributeReader}.
   * This reads in the specifications using the format:
   * {
   *   u2 point_pc;
   *   u2 order;
   *   formula_info invariant;
   *   formula_info variant;
   * }
   * see section "LoopSpecificationTable Attribute" in "BML Reference Manual",
   * but the fields <code>point_pc</code> and <code>order</code> should
   * be read by the caller of the current method.
   *
   * @param m a method containing this annotation
   * @param ar a stream to load the loop specification from
   * @return the single loop specification loaded from the given attribute
   *   reader
   * @throws ReadAttributeException - if data left in <code>ar</code> does not
   *   represent a correct loop specification
   */
  @Override
  protected InCodeAnnotation loadSingle(final BCMethod m,
                                       final AttributeReader ar)
    throws ReadAttributeException {
    final AbstractFormula invariant = ar.readFormula();
    final BCExpression decreases = ar.readExpression();
    return new SingleLoopSpecification(m, null, -1, invariant,
                                       decreases);
  }

  /**
   * @return the type of the annotation (used to filter annotations of this
   *   kind)
   */
  @Override
  protected int singleType() {
    return AType.C_LOOPSPEC;
  }

  /**
   * Saves a single loop specification to an {@link AttributeWriter}.
   *
   * @param icannot the annotation to write to the writer to
   * @param aw a stream to write the annotation to
   */
  @Override
  protected void saveSingle(final InCodeAnnotation icannot,
                            final AttributeWriter aw) {
    final SingleLoopSpecification sls = (SingleLoopSpecification) icannot;
    sls.getInvariant().write(aw);
    sls.getVariant().write(aw);
  }


}
