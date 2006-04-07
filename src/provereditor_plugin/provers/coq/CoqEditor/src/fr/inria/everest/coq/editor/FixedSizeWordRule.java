package fr.inria.everest.coq.editor;

import org.eclipse.jface.text.rules.ICharacterScanner;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.IWordDetector;
import org.eclipse.jface.text.rules.Token;
import org.eclipse.jface.text.rules.WordRule;

public class FixedSizeWordRule extends WordRule {
	int fSize = 0;
	/** Buffer used for pattern detection */
	private StringBuffer fBuffer= new StringBuffer();
	
	public FixedSizeWordRule(IWordDetector detector, int size) {
		super(detector);
		fSize = size;
	}
	
	public IToken evaluate(ICharacterScanner scanner) {
		int c= scanner.read();
		if (fDetector.isWordStart((char) c)) {
			if (fColumn == UNDEFINED || (fColumn == scanner.getColumn() - 1)) {

				fBuffer.setLength(0);
				int i = 0;
				do {
					fBuffer.append((char) c);
					c= scanner.read();
					i++;
				} while (c != ICharacterScanner.EOF && fDetector.isWordPart((char) c) && (i < fSize));
				scanner.unread();

				IToken token= (IToken) fWords.get(fBuffer.toString());
				if (token != null)
					return token;

				if (fDefaultToken.isUndefined())
					unreadBuffer(scanner);

				return fDefaultToken;
			}
		}

		scanner.unread();
		return Token.UNDEFINED;
	}
	/**
	 * Returns the characters in the buffer to the scanner.
	 *
	 * @param scanner the scanner to be used
	 */
	protected void unreadBuffer(ICharacterScanner scanner) {
		for (int i= fBuffer.length() - 1; i >= 0; i--)
			scanner.unread();
	}
}
