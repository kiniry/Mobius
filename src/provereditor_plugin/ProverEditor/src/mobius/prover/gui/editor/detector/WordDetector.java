package mobius.prover.gui.editor.detector;

import org.eclipse.jface.text.rules.IWordDetector;

/**
 * A basic implementation to detect words for a prover.
 */
public class WordDetector implements IWordDetector {

	/*
	 *  (non-Javadoc)
	 * @see org.eclipse.jface.text.rules.IWordDetector#isWordStart(char)
	 */
	public boolean isWordStart(char c) {
		return Character.isLetter(c);
	}

	/*
	 *  (non-Javadoc)
	 * @see org.eclipse.jface.text.rules.IWordDetector#isWordPart(char)
	 */
	public boolean isWordPart(char c) {
		return Character.isLetterOrDigit(c) || c== '_';
	}

}
