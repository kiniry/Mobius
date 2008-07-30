package annot.bcexpression.modifies;

import annot.bcexpression.BCExpression;
import annot.io.AttributeReader;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;

/**
 * This class describes modification of single element
 * of an array.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class ModifiesSingleIndex extends SpecArray {

  /**
   * A constructor from AttributeReader.
   *
   * @param ar - input stream to load from,
   * @param root - type of this expression, should be
   *     {@link Code#MODIFIES_SINGLE_INDEX}.
   * @throws ReadAttributeException - if root + stream
   *     in <code>ar</code> doesn't represent correct
   *     array modification specification.
   */
  public ModifiesSingleIndex(final AttributeReader ar, final int root)
    throws ReadAttributeException {
    super(ar, root);
  }

  /**
   * A standard constructor.
   *
   * @param index - expression that evaluates to the
   *     modifies index.
   */
  public ModifiesSingleIndex(final BCExpression index) {
    super(Code.MODIFIES_SINGLE_INDEX, index);
  }

  @Override
  protected String printCode1(final BMLConfig conf) {
    return getSubExpr(0).printRawCode(conf);
  }

  @Override
  protected void read(final AttributeReader ar, final int root)
    throws ReadAttributeException {
    setSubExprCount(1);
    final BCExpression index = ar.readExpression();
    setSubExpr(0, index);
  }

  @Override
  public String toString() {
    return "[" + getSubExpr(0).toString() + "]";
  }

}
