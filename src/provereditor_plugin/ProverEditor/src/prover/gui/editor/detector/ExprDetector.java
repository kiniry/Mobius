package prover.gui.editor.detector;

import org.eclipse.jface.text.rules.IWordDetector;
/**
 * A basic implementation of a detector to detect expressions for a prover.
 */
public class ExprDetector implements IWordDetector {

	/*
	 *  (non-Javadoc)
	 * @see org.eclipse.jface.text.rules.IWordDetector#isWordStart(char)
	 */
	public boolean isWordStart(char c) {
		return c == '-' || c == '<' ||c == '>' ||
			c == ':' || c == '.' ||c == ',';
	}

	/*
	 *  (non-Javadoc)
	 * @see org.eclipse.jface.text.rules.IWordDetector#isWordPart(char)
	 */
	public boolean isWordPart(char c) {
		return isWordStart(c);
	}

}
