package annot.attributes;

import annot.bcclass.BCMethod;
import annot.bcexpression.BCExpression;
import annot.bcexpression.formula.AbstractFormula;
import annot.bcexpression.modifies.ModifyList;
import annot.io.AttributeReader;
import annot.io.ReadAttributeException;
import annot.textio.AttributeNames;

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

}
