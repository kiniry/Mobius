package annot.bcexpression;

import annot.bcclass.BCClass;
import annot.bcexpression.javatype.JavaReferenceType;
import annot.bcexpression.javatype.JavaType;
import annot.io.Code;
import annot.textio.BMLConfig;
import annot.textio.DisplayStyle;

/**
 * This class represents <code>this</code> expression.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class THIS extends BCExpression {

  /**
   * BCClass this expression represents.
   */
  private final BCClass bcc;

  /**
   * A standard constructor.
   *
   * @param classRepresentation - initializing class.
   */
  public THIS(final BCClass classRepresentation) {
    super(Code.THIS);
    this.bcc = classRepresentation;
  }

  /**
   * This method returns the type of this expression provided that all
   * the subexpressions have correct types. In this case, this is
   * the type of the object in which the identifier <code>this</code> is used
   * and no subexpressions are checked.
   *
   * @return the type of the object in which the identifier is used.
   */
  protected JavaType checkType1() {
    return getType1();
  }

  /**
   * @return BCClass this expression represents.
   */
  public BCClass getBcc() {
    return this.bcc;
  }

  /**
   * This method returns the type of this expression. In this case, this is
   * the type of the object in which the identifier <code>this</code> is used.
   *
   * @return the type of the method with this result
   */
  public JavaType getType1() {
    return JavaReferenceType.ANY;
  }

  /**
   * Returns the string representation of the expression which is
   * contained in {@link DisplayStyle#THIS_KWD}.
   *
   * @param conf - see {@link BMLConfig}.
   * @return {@link DisplayStyle#THIS_KWD}
   */
  protected String printCode1(final BMLConfig conf) {
    return DisplayStyle.THIS_KWD;
  }

  /**
   * @return simple String representation of this
   *     expression, for debugging only.
   */
  public String toString() {
    return DisplayStyle.THIS_KWD;
  }

}
