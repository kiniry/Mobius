package annot.bcexpression.modifies;

import annot.bcexpression.BCExpression;
import annot.io.AttributeReader;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;

/**
 * This class represents array modification specificatoin.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class ModifiesArray extends ModifyExpression {

  /**
   * A constructor from AttributeReader.
   *
   * @param ar - input stream to load from,
   * @param root - type of this expression, should be
   *     {@link Code#MODIFIES_ARRAY}.
   * @throws ReadAttributeException - if root + stream
   *     in <code>ar</code> doesn't represent correct
   *     ModifyArrayExpression.
   */
  public ModifiesArray(final AttributeReader ar, final int root)
    throws ReadAttributeException {
    super(ar, root);
  }

  /**
   * A standard constructor.
   *
   * @param me - an array variable,
   * @param sa - specifies which array's elements can be
   *     modified.
   */
  public ModifiesArray(final ModifyExpression me, final SpecArray sa) {
    super(Code.MODIFIES_ARRAY, me, sa);
  }

  @Override
  protected String printCode1(final BMLConfig conf) {
    return getSubExpr(0).printCode(conf) + "[" +
      getSubExpr(1).printRawCode(conf) + "]";
  }

  @Override
  protected void read(final AttributeReader ar, final int root)
    throws ReadAttributeException {
    setSubExprCount(2);
    final BCExpression array = ar.readModifyExpression();
    final BCExpression index = ar.readSpecArray();
    setSubExpr(0, array);
    setSubExpr(1, index);
  }

  @Override
  public String toString() {
    return getSubExpr(0).toString() + getSubExpr(1).toString();
  }

}
