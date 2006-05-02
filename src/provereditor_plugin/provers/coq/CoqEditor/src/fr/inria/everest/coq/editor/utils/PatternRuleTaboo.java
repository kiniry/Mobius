package fr.inria.everest.coq.editor.utils;

import org.eclipse.jface.text.rules.ICharacterScanner;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.MultiLineRule;
import org.eclipse.jface.text.rules.Token;

public class PatternRuleTaboo extends MultiLineRule {
	public PatternRuleTaboo(String startSequence, String endSequence, IToken token) {
		super(startSequence, endSequence, token, (char) 0);
	}

	/**
	 * Evaluates this rules without considering any column constraints. Resumes
	 * detection, i.e. look sonly for the end sequence required by this rule if the
	 * <code>resume</code> flag is set.
	 *
	 * @param scanner the character scanner to be used
	 * @param resume <code>true</code> if detection should be resumed, <code>false</code> otherwise
	 * @return the token resulting from this evaluation
	 * @since 2.0
	 */
	protected IToken doEvaluate(ICharacterScanner scanner, boolean resume) {

		if (resume) {

			if (endSequenceDetected(scanner))
				return fToken;


		} else {

			int c= scanner.read();
			if (c == fStartSequence[0]) {
				if (sequenceDetected(scanner, fStartSequence, false)) {
					if (endSequenceDetected(scanner))
						return fToken;
					else
						for(int i = 0; i < fStartSequence.length -1; i++)
							scanner.unread();
				}

				
			}
		}
		scanner.unread();
		
		return Token.UNDEFINED;
	}

	/**
	 * Returns whether the end sequence was detected. As the pattern can be considered
	 * ended by a line delimiter, the result of this method is <code>true</code> if the
	 * rule breaks on the end of the line, or if the EOF character is read.
	 *
	 * @param scanner the character scanner to be used
	 * @return <code>true</code> if the end sequence has been detected
	 */
	protected boolean endSequenceDetected(ICharacterScanner scanner) {
		
	
		int c; int count = 0;
		while ((c= scanner.read()) != ICharacterScanner.EOF && (c != '=')) {
			count ++;
			if (c == fEscapeCharacter) {
				// Skip escaped character(s)
				if (fEscapeContinuesLine) {
					c= scanner.read();
				} else {
					scanner.read();
				}
				count ++;

			} else if (fEndSequence.length > 0 && c == fEndSequence[0]) {
				// Check if the specified end sequence has been found.
				if (sequenceDetected(scanner, fEndSequence, true))
					return true;
			}
		}
		for(int i = 0; i < count + 1; i++)
			scanner.unread();
		return false;
	}


}