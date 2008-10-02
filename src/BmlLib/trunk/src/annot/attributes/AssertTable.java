package annot.attributes;

import annot.bcclass.BCMethod;
import annot.bcexpression.formula.AbstractFormula;
import annot.io.AttributeReader;
import annot.io.ReadAttributeException;
import annot.textio.DisplayStyle;

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
   * @return Unknown (BCEL) attribute name. TODO unknown dla kogo
   */
  @Override
  public String getName() {
    return DisplayStyle.ASSERT_TABLE_ATTR;
  }

  /**
   * Loads single assert from a file.
   *
   * @param m - a method containing this attribute,
   * @param ar - a stream to load the assert from.
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
   * @return attribute type of a single annotation.
   */
  @Override
  protected int singleType() {
    return AType.C_ASSERT;
  }

}
