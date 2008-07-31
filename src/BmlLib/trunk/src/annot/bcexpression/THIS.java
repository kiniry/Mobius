package annot.bcexpression;

import annot.bcclass.BCClass;
import annot.bcexpression.javatype.JavaReferenceType;
import annot.bcexpression.javatype.JavaType;
import annot.io.Code;
import annot.textio.BMLConfig;

/**
 * This class represents <code>'this'</code> expression.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class THIS extends OldExpression {

  /**
   * BCClass this expression represents.
   */
  private final BCClass bcc;

  /**
   * A standard constructor.
   *
   * @param isOld - whether it should be OLD_THIS or THIS,
   * @param classRepresentation - initializing class.
   */
  public THIS(final boolean isOld,
              final BCClass classRepresentation) {
    super(isOld ? Code.OLD_THIS : Code.THIS, isOld);
    this.bcc = classRepresentation;
  }

  @Override
  protected JavaType checkType2() {
    return getType();
  }

  /**
   * @return BCClass this expression represents.
   */
  public BCClass getBcc() {
    return this.bcc;
  }

  @Override
  public JavaType getType1() {
    return JavaReferenceType.ANY;
  }

  @Override
  protected String printCode1(final BMLConfig conf) {
    return isOld() ? "old_this" : "this";
  }

  @Override
  public String toString() {
    return isOld() ? "old_this" : "this";
  }

}
