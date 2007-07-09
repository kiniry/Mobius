/*
 * Created on 2005-05-13
 */
package umbra.editor.parsing;

import org.eclipse.jface.text.rules.ICharacterScanner;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.NumberRule;
import org.eclipse.jface.text.rules.Token;

/**
 * Modified NumberRule that allows an additional mark before
 * (or after) the number to be read (used with '#' and '%').
 *
 * @author Wojciech Wąs  (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */
public class SpecialNumberRule extends NumberRule {

  /**
   * TODO.
   */
  char start;
  /**
   * TODO.
   */
  char fin;
  /**
   * TODO.
   */
  boolean isFin;

  /**
   * TODO.
   * @param a_start TODO
   * @param an_end TODO
   * @param a_token TODO
   * @see NumberRule#NumberRule(IToken)
   */
  public SpecialNumberRule(final char a_start,
                           final char an_end,
                           final IToken a_token) {
    super(a_token);
    this.start = a_start;
    this.fin = an_end;
    isFin = true;
  }

  /**
   * TODO.
   * @param a_start TODO
   * @param a_token TODO
   */
  public SpecialNumberRule(final char a_start, final IToken a_token) {
    super(a_token);
    this.start = a_start;
    isFin = false;
  }

  /**
   * TODO.
   * @param a_scanner the character scanner to be used to obtain the token
   * @return the recognized token (supplied in the constructor) or
   *         {@ref Token#UNDEFINED} in case the rule does not apply
   * @see NumberRule#evaluate(ICharacterScanner)
   */
  public final IToken evaluate(final ICharacterScanner a_scanner) {
    int c = a_scanner.read();
    if ((char)c == start) {
      if (super.evaluate(a_scanner) == fToken) {
        if (!isFin) return fToken;
        c = a_scanner.read();
        if ((char)c == fin) return fToken;
        do {
          a_scanner.unread();
          a_scanner.unread();
          c = a_scanner.read();
        } while (Character.isDigit((char) c));
      }
    }
    a_scanner.unread();
    return Token.UNDEFINED;
  }
}
