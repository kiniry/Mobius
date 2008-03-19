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
 */
public class ModifiesLocalVar extends ModifyExpression {

  /**
   * Creates the local variable modifies expression for the given
   * {@link LocalVariable} object.
   *
   * @param a_var the local variable represented by the expression
   */
  public ModifiesLocalVar(LocalVariable a_var) {
    super(Code.MODIFIES_LOCAL_VARIABLE, a_var);
  }

  public ModifiesLocalVar(AttributeReader reader, int root) 
    throws ReadAttributeException {
    super(reader, root);
  }

  /* (non-Javadoc)
   * @see annot.bcexpression.BCExpression#printCode1(annot.textio.BMLConfig)
   */
  @Override
  protected String printCode1(BMLConfig conf) {
    return getSubExpr(0).printCode(conf);
  }

  /* (non-Javadoc)
   * @see annot.bcexpression.BCExpression#toString()
   */
  @Override
  public String toString() {
    return getSubExpr(0).toString();
  }

  /* (non-Javadoc)
   * @see annot.bcexpression.BCExpression#read(AttributeReader, int)
   */
  @Override
  protected void read(AttributeReader ar, int root)
      throws ReadAttributeException {
    setSubExprCount(1);
    BCExpression lv = ar.readExpression();
    setSubExpr(0, lv);
  }
}
