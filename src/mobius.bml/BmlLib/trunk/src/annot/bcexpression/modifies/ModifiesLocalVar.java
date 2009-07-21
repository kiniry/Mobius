/**
 *
 */
package annot.bcexpression.modifies;

import annot.bcexpression.BCExpression;
import annot.bcexpression.LocalVariable;
import annot.io.AttributeReader;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;

/**
 * This class represents the modifies expression with a local variable.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class ModifiesLocalVar extends ModifyExpression {

  public ModifiesLocalVar(final AttributeReader reader, final int root)
    throws ReadAttributeException {
    super(reader, root);
  }

  /**
   * Creates the local variable modifies expression for the given
   * {@link LocalVariable} object.
   *
   * @param a_var the local variable represented by the expression
   */
  public ModifiesLocalVar(final LocalVariable a_var) {
    super(Code.MODIFIES_LOCAL_VARIABLE, a_var);
  }

  /* (non-Javadoc)
   * @see annot.bcexpression.BCExpression#printCode1(annot.textio.BMLConfig)
   */
  @Override
  protected String printCode1(final BMLConfig conf) {
    return getSubExpr(0).printCode(conf);
  }

  /* (non-Javadoc)
   * @see annot.bcexpression.BCExpression#read(AttributeReader, int)
   */
  @Override
  protected void read(final AttributeReader ar, final int root)
    throws ReadAttributeException {
    setSubExprCount(1);
    final BCExpression lv = ar.readExpression();
    setSubExpr(0, lv);
  }

  /* (non-Javadoc)
   * @see annot.bcexpression.BCExpression#toString()
   */
  @Override
  public String toString() {
    return getSubExpr(0).toString();
  }
}
