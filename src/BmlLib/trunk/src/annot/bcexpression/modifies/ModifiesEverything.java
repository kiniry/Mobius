package annot.bcexpression.modifies;

import annot.io.Code;
import annot.textio.BMLConfig;

/**
 * This class represents any side effect of described code,
 * or that side effects are unknown.
 * This is a singleton, it has only one instance
 * ({@link ModifyExpression#Everything}).
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class ModifiesEverything extends ModifyExpression {

  /**
   * The text of the \everything modify expression.
   */
  private static final String EVERYTHING_KEYWORD_TEXT = "\\everything";

  /**
   * A constructor for superclass only. Use
   * {@link ModifyExpression#Everything} instead.
   */
  protected ModifiesEverything() {
    super(Code.MODIFIES_EVERYTHING);
  }

  @Override
  protected String printCode1(final BMLConfig conf) {
    return EVERYTHING_KEYWORD_TEXT;
  }

  @Override
  public String toString() {
    return EVERYTHING_KEYWORD_TEXT;
  }

}
