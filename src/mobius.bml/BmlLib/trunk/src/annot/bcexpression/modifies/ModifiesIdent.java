package annot.bcexpression.modifies;

import annot.bcexpression.BCExpression;
import annot.io.AttributeReader;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;

/**
 * This class represents modification of a single variable
 * (local variable or field).
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class ModifiesIdent extends ModifyExpression {

  /**
   * A constructor from AttributeReader.
   *
   * @param ar input stream to load from,
   * @param root - type of this expression, should be
   *     {@link Code#MODIFIES_DOT}.
   * @throws ReadAttributeException - if stream in
   * <code>ar</code> doesn't represent correct exrpession.
   */
  public ModifiesIdent(final AttributeReader ar, final int root)
    throws ReadAttributeException {
    super(ar, root);
  }

  /**
   * A standard constructor.
   *
   * @param expr - expression whose modification this
   *     modify expression will describe. Should be
   *     a variable (eg. local variable or field).
   */
  public ModifiesIdent(final BCExpression expr) {
    super(Code.MODIFIES_IDENT, expr);
  }

  @Override
  protected String printCode1(final BMLConfig conf) {
    return getSubExpr(0).printCode(conf);
  }

  @Override
  protected void read(final AttributeReader ar, final int root)
    throws ReadAttributeException {
    setSubExprCount(1);
    final BCExpression expr = ar.readExpression();
    setSubExpr(0, expr);
  }

  @Override
  public String toString() {
    return getSubExpr(0).toString();
  }

}
