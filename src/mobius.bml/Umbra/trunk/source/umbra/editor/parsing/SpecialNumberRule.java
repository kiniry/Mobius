/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.editor.parsing;

import org.eclipse.jface.text.rules.ICharacterScanner;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.NumberRule;
import org.eclipse.jface.text.rules.Token;

/**
 * The text styling rule which extends the {@link NumberRule} so that it
 * allows an additional mark before (and optionally after) the number to be read
 * (used with '#' and '%').
 *
 * @author Wojciech Wąs  (ww209224@students.mimuw.edu.pl)
 * @author Aleksy Schubert  (alx@mimuw.edu.pl)
 * @version a-01
 */
public class SpecialNumberRule extends NumberRule {

  /**
   * The mark preceding the number.
   */
  private char my_start_char;

  /**
   * The mark after the number.
   */
  private char my_fin;

  /**
   * The flag is <code>true</code> in case the final character should be
   * checked.
   */
  private boolean my_isfin_flag;

  /**
   * The constructor creates the rule such that the number is recognised when
   * it is preceded with <code>a_start</code> character and finished with
   * the <code>an_end</code> character. The token parameter is the token which
   * is returned when the rule is successful.
   *
   * @param a_start the mark preceding the number
   * @param an_end the mark after the number
   * @param a_token the token to be returned in case the rule is successfully
   *   evaluated
   * @see NumberRule#NumberRule(IToken)
   */
  public SpecialNumberRule(final char a_start,
                           final char an_end,
                           final IToken a_token) {
    super(a_token);
    this.my_start_char = a_start;
    this.my_fin = an_end;
    my_isfin_flag = true;
  }

  /**
   * The constructor creates the rule such that the number is recognised when
   * it is preceded with <code>a_start</code> character and no final character
   * is to be checked. The token parameter is the token which is returned when
   * the rule is successful.
   *
   * @param a_start the mark preceding the number
   * @param a_token the token to be returned in case the rule is successfully
   *   evaluated
   * @see NumberRule#NumberRule(IToken)
   */
  public SpecialNumberRule(final char a_start, final IToken a_token) {
    super(a_token);
    this.my_start_char = a_start;
    my_isfin_flag = false;
  }

  /**
   * Evaluates the rule to check the number with starting and final marks.
   * The method scans the first character and checks if the character is
   * the starting character of the rule. If so, it swallows a number. If
   * the scanning of the number is successful the method checks if it must
   * check the final character. If not, it returns successfully. If so it
   * checks the final character. In case it matches the proper final character
   * the method returns successfully. Otherwise, it puts back the final
   * character, the characters of the number and the starting character
   * to the scanner.
   *
   * The token returned by this rule returns <code>true</code> when calling
   * <code>isUndefined</code>, if the text that the rule investigated does not
   * match the rule's requirements.

   * @param a_scanner the character scanner to be used to obtain the token
   * @return the recognised token (supplied in the constructor) or
   *         {@link Token#UNDEFINED} in case the rule does not apply
   * @see NumberRule#evaluate(ICharacterScanner)
   */
  public final IToken evaluate(final ICharacterScanner a_scanner) {
    int c = a_scanner.read();
    if ((char)c == my_start_char) {
      if (super.evaluate(a_scanner) == fToken) {
        if (!my_isfin_flag) return fToken;
        c = a_scanner.read();
        if ((char)c == my_fin) return fToken;
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
