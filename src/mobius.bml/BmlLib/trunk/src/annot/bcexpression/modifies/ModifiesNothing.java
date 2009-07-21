package annot.bcexpression.modifies;

import annot.io.Code;
import annot.textio.BMLConfig;

/**
 * This class represents no side effect of described code.
 * This is a singleton, it has only one instance
 * ({@link ModifyExpression#Nothing}).
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class ModifiesNothing extends ModifyExpression {

  /**
   * The text of the \nothing modify expression.
   */
  private static final String NOTHING_KEYWORD_TEXT = "\\nothing";

  /**
   * A constructor for superclass only. Use
   * {@link ModifyExpression#Nothing} instead.
   */
  protected ModifiesNothing() {
    super(Code.MODIFIES_NOTHING);
  }

  @Override
  protected String printCode1(final BMLConfig conf) {
    return NOTHING_KEYWORD_TEXT;
  }

  @Override
  public String toString() {
    return NOTHING_KEYWORD_TEXT;
  }

}
