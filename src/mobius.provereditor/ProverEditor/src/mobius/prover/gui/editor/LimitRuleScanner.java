package mobius.prover.gui.editor;

import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.Token;


/**
 * A specific scanner that highlight text using the specified rules.
 * It sets a background color different from the beginning of the
 * text to a specified limit than from the limit to the end of the
 * text. The first part is highlighted with the color 
 * {@link IColorConstants#HILIT_COLOR} the second part with the color
 * {@link IColorConstants#NORMAL_COLOR}. 
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class LimitRuleScanner extends BasicRuleScanner implements IColorConstants {
  /** the limit to which the background shall be different. */
  private int fLimit;

  /**
   * Create a new rule scanner.
   */
  public LimitRuleScanner() {
    this(null);
  }
  
  /**
   * Create a new rule scanner, with the given rules.
   * @param rules the rules to set the colors
   */
  public LimitRuleScanner(final IRule[] rules) {
    super();
    
    if (rules == null) {
      setRules(new IRule[0]);
    }
    else {
      setRules(rules);
    }
    setDefaultReturnToken(new Token(
      new BasicTextAttribute(DEFAULT_TAG_COLOR)));
  }
  
  /** {@inheritDoc} */
  @Override
  public IToken nextToken() {
    fTokenOffset = fOffset;
    final IToken tok = getNextToken(fTokenOffset);
    if (tok.equals(Token.EOF)) {
      return tok;
    }
    if (fTokenOffset < fLimit) {
      ((BasicTextAttribute)tok.getData()).setBackground(HILIT_COLOR);
    }
    else {
      ((BasicTextAttribute)tok.getData()).setBackground(NORMAL_COLOR);
    }
    return tok;
  }
  
  /**
   * Returns the next token found. 
   * @param off the offset where to start looking at
   * @return the token without the specific background color
   */
  private IToken getNextToken(final int off) {
    fColumn = UNDEFINED;
    if (fRules != null) {
      for (int i = 0; i < fRules.length; i++) {
        final IToken token = fRules[i].evaluate(this);
        if (!token.isUndefined()) {
          return token;
        }
      }
    }

    if (read() == EOF) {
      return Token.EOF;
    }
    return fDefaultReturnToken;
  }
  
  /**
   * Set the limit to which the background shall be different.
   * @param l the offset where to divide the two parts of the
   * text
   */
  public void setLimit(final int l) {
    fLimit  = l;
  }
  /**
   * Return the limit dividing the two highlighted differently part.
   * @return a valid offset
   */
  public  int getLimit() {
    return fLimit;
  }

}
