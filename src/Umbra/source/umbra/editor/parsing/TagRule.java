package umbra.editor.parsing;

import org.eclipse.jface.text.rules.ICharacterScanner;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.MultiLineRule;
import org.eclipse.jface.text.rules.Token;

import umbra.UmbraHelper;
import umbra.UmbraPlugin;

/**
 * TODO
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
   * TODO
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
   * TODO
   * @see PatternRule#sequenceDetected(ICharacterScanner, char[], boolean)
   */
  protected final boolean sequenceDetected (final ICharacterScanner scanner,
                                            final char[] sequence,
                                            final boolean eofAllowed) {
    UmbraPlugin.messagelog("TagRule#sequenceDetected: " + new String(sequence));
    final int c = scanner.read();
    if (sequence[0] == '<') {
      if (c == '?') {
        // processing instruction - abort
        scanner.unread();
        return false;
      }
      if (c == '!') {
        //scanner.unread();
        // comment - abort
        //return false;
      }
    } else if (sequence[0] == '>') {
      scanner.unread();
    }
    return super.sequenceDetected(scanner, sequence, eofAllowed);
  }

  /**
   * TODO
   */
  protected final IToken doEvaluate(final ICharacterScanner scanner,
                                    final boolean resume) {
    UmbraPlugin.messagelog("TagRule#doEvaluate: ");
    if (resume) {

      if (endSequenceDetected(scanner))
        return fToken;

    } else {

      int c = scanner.read();
      if (c == fStartSequence[0]) {
        if (sequenceDetected(scanner, fStartSequence, false)) {
          my_loop++;
          int wrong = 0, i = 0;
          while (my_loop > 0 && my_loop < LOOP_BOUND && wrong < WRONG_BOUND) {
            c = scanner.read();
            i++;
            if (c == fStartSequence[0]) {
              if (sequenceDetected(scanner, fStartSequence, false)) {
                my_loop++;
                wrong++;
              }
            } else if (c == fEndSequence[0]) {
              if (sequenceDetected(scanner, fEndSequence, false)) {
                my_loop--;
                if (my_loop == 0) return fToken;
              }
            }
          }
          for (; i > 0; i--) scanner.unread();
        }
      }
    }

    scanner.unread();
    return Token.UNDEFINED;
  }
}
