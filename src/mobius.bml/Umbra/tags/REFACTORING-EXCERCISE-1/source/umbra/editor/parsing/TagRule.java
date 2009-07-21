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
import org.eclipse.jface.text.rules.MultiLineRule;
import org.eclipse.jface.text.rules.Token;

import umbra.UmbraPlugin;

/**
 * TODO.
 *
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @author Tomek Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @version a-01
 */
public class TagRule extends MultiLineRule {

  /**
   * TODO.
   */
  private static final int WRONG_BOUND = 100;

  /**
   * TODO.
   */
  private static final int LOOP_BOUND = 100;

  /**
   * TODO.
   */
  int my_loop;

  /**
   * This constructor creates a {@ref MultiLineRule} the start of which
   * is "<" and the end of which is ">".
   *
   * @param a_token token the token to be returned on success
   * @see MultiLineRule#MultiLineRule(String, String, IToken)
   */
  public TagRule(final IToken a_token) {
    super("<", ">", a_token);
    UmbraPlugin.messagelog("TagRule constructor");
  }

  /**
   * TODO.
   *
   * @param a_scanner TODO
   * @param a_sequence TODO
   * @param an_eof_allowed_flag TODO
   * @return TODO
   * @see PatternRule#sequenceDetected(ICharacterScanner, char[], boolean)
   */
  protected final boolean sequenceDetected (final ICharacterScanner a_scanner,
                                            final char[] a_sequence,
                                            final boolean an_eof_allowed_flag) {
    UmbraPlugin.messagelog("TagRule#sequenceDetected: " +
                           new String(a_sequence));
    final int c = a_scanner.read();
    if (a_sequence[0] == '<') {
      if (c == '?') {
        // processing instruction - abort
        a_scanner.unread();
        return false;
      }
      if (c == '!') {
        //scanner.unread();
        // comment - abort
        //return false;
        UmbraPlugin.messagelog("sequenceDetected with !");
      }
    } else if (a_sequence[0] == '>') {
      a_scanner.unread();
    }
    return super.sequenceDetected(a_scanner, a_sequence, an_eof_allowed_flag);
  }

  /**
   * TODO.
   * @param a_scanner the character scanner to be used to obtain the token
   * @param a_resume_flag <code>true</code> if detection of a token should
   *                      be resumed i.e. it looks for the end sequence of
   *                      the rule
   * @return the recognized token (supplied in the constructor) or
   *         {@ref Token#UNDEFINED} in case the rule does not apply
   * @see org.eclipse.jface.text.rules.PatternRule#doEvaluate(ICharacterScanner,
   *                                                          boolean)
   */
  protected final IToken doEvaluate(final ICharacterScanner a_scanner,
                                    final boolean a_resume_flag) {
    UmbraPlugin.messagelog("TagRule#doEvaluate: ");
    if (a_resume_flag) {
      if (endSequenceDetected(a_scanner))
        return fToken;
    } else {
      int c = a_scanner.read();
      if (c == fStartSequence[0]) {
        if (sequenceDetected(a_scanner, fStartSequence, false)) {
          my_loop++;
          int wrong = 0, i = 0;
          while (my_loop > 0 && my_loop < LOOP_BOUND && wrong < WRONG_BOUND) {
            c = a_scanner.read();
            i++;
            if (c == fStartSequence[0]) {
              if (sequenceDetected(a_scanner, fStartSequence, false)) {
                my_loop++;
                wrong++;
              }
            } else if (c == fEndSequence[0]) {
              if (sequenceDetected(a_scanner, fEndSequence, false)) {
                my_loop--;
                if (my_loop == 0) return fToken;
              }
            }
          }
          for (; i > 0; i--) a_scanner.unread();
        }
      }
    }
    a_scanner.unread();
    return Token.UNDEFINED;
  }
}
