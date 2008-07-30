package annot.bcexpression.modifies;

import annot.bcexpression.BCExpression;
import annot.io.AttributeReader;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;

/**
 * This class represents {@link FieldAccess}
 * as a {@link ModifyExpression} (modifiyExpression in form:
 * modifyExpression . expression,
 * where expression should be a variable.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class ModifiesDot extends ModifyExpression {

  /**
   * A constructor from AttributeReader.
   *
   * @param ar - input stream to load from,
   * @param root - type of this expression, should be
   *     {@link Code#MODIFIES_DOT}.
   * @throws ReadAttributeException - if root + stream
   *     in <code>ar</code> doesn't represent correct
   *     ModifyDotExpression.
   */
  public ModifiesDot(final AttributeReader ar, final int root)
    throws ReadAttributeException {
    super(ar, root);
  }

  /**
   * A standard construcotr.
   *
   * @param left - left subexpression (may contain dots),
   * @param right - right subexpression, without dots
   *     nor arrays.
   */
  public ModifiesDot(final ModifyExpression left, final BCExpression right) {
    super(Code.MODIFIES_DOT, left, right);
  }

  @Override
  protected String printCode1(final BMLConfig conf) {
    return getSubExpr(0).printCode(conf) + "." + getSubExpr(1).printCode(conf);
  }

  @Override
  protected void read(final AttributeReader ar, final int root)
    throws ReadAttributeException {
    setSubExprCount(2);
    final ModifyExpression left = ar.readModifyExpression();
    final BCExpression right = ar.readExpression();
    setSubExpr(0, left);
    setSubExpr(1, right);
  }

  @Override
  public String toString() {
    return getSubExpr(0).toString() + "." + getSubExpr(1).toString();
  }

}
