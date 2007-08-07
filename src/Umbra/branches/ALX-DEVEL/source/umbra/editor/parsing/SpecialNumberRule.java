/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
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
  char my_start_char;
  /**
   * TODO.
   */
  char my_fin;
  /**
   * TODO.
   */
  boolean my_isfin_flag;

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
    this.my_start_char = a_start;
    this.my_fin = an_end;
    my_isfin_flag = true;
  }

  /**
   * TODO.
   * @param a_start TODO
   * @param a_token TODO
   */
  public SpecialNumberRule(final char a_start, final IToken a_token) {
    super(a_token);
    this.my_start_char = a_start;
    my_isfin_flag = false;
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
