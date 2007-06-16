package umbra.editor.parsing;

import org.eclipse.jface.text.rules.*;

/**
 * TODO
 */
public class TagRule extends MultiLineRule {

  /**
   * TODO
   */
  int loop = 0;

  /**
   * TODO
   */
  public TagRule(final IToken token) {
    super("<", ">", token);
  }

  /**
   * TODO
   */
  protected final boolean sequenceDetected(
    final ICharacterScanner scanner,
    final char[] sequence,
    final boolean eofAllowed) {
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
  protected final IToken doEvaluate(final ICharacterScanner scanner, final boolean resume) {

    if (resume) {

      if (endSequenceDetected(scanner))
        return fToken;

    } else {

      int c= scanner.read();
      if (c == fStartSequence[0]) {
        if (sequenceDetected(scanner, fStartSequence, false)) {
          loop++;
          int wrong = 0, i = 0;
          while (loop > 0 && loop < 100 && wrong < 100) {
            c = scanner.read();
            i++;
            if (c == fStartSequence[0]) {
              if (sequenceDetected(scanner, fStartSequence, false)) {
                loop++;
                wrong++;
              }
            }
            else if (c == fEndSequence[0]) {
              if (sequenceDetected(scanner, fEndSequence, false)) {
                loop--;
                if (loop == 0) return fToken;
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
