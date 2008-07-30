package annot.bcexpression.modifies;

import annot.bcexpression.BCExpression;
import annot.io.AttributeReader;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;

/**
 * This class describes modification of an array elements
 * from one index to another.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class ModifiesInterval extends SpecArray {

  /**
   * A constructor from AttributeReader.
   *
   * @param ar - input stream to load from,
   * @param root - type of this expression, should be
   *     {@link Code#MODIFIES_INTERVAL}.
   * @throws ReadAttributeException - if root + stream
   *     in <code>ar</code> doesn't represent correct
   *     array modification specification.
   */
  public ModifiesInterval(final AttributeReader ar, final int root)
    throws ReadAttributeException {
    super(ar, root);
  }

  /**
   * A standard constructor.
   *
   * @param from - expression that evaluates to beginning
   *     of the changes (first affected array index).
   * @param to - expression that evaluates to end
   *     of the changes (last affected array index).
   */
  public ModifiesInterval(final BCExpression from, final BCExpression to) {
    super(Code.MODIFIES_INTERVAL, from, to);
  }

  @Override
  protected String printCode1(final BMLConfig conf) {
    return getSubExpr(0).printRawCode(conf) + " .. " +
      getSubExpr(1).printRawCode(conf);
  }

  @Override
  protected void read(final AttributeReader ar, final int root)
    throws ReadAttributeException {
    setSubExprCount(2);
    final BCExpression from = ar.readExpression();
    final BCExpression to = ar.readExpression();
    setSubExpr(0, from);
    setSubExpr(1, to);
  }

  @Override
  public String toString() {
    return getSubExpr(0).toString() + " .. " + getSubExpr(1).toString();
  }

}
