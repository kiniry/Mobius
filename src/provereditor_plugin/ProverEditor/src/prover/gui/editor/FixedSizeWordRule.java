package prover.gui.editor;

import org.eclipse.jface.text.rules.ICharacterScanner;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.IWordDetector;
import org.eclipse.jface.text.rules.Token;
import org.eclipse.jface.text.rules.WordRule;

/**
 * A rule to detect words of a fixed size.
 */
public class FixedSizeWordRule extends WordRule {
	/** the size of the word */
	private int fSize = 0;
	/** Buffer used for pattern detection */
	private StringBuffer fBuffer= new StringBuffer();
	
	/**
	 * Create a new word rule.
	 * @param detector a word detector
	 * @param size the size of a word
	 */
	public FixedSizeWordRule(IWordDetector detector, int size) {
		super(detector);
		fSize = size;
	}
	
	
	/*
	 *  (non-Javadoc)
	 * @see org.eclipse.jface.text.rules.IRule#evaluate(org.eclipse.jface.text.rules.ICharacterScanner)
	 */
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

	/*
	 *  (non-Javadoc)
	 * @see org.eclipse.jface.text.rules.WordRule#unreadBuffer(org.eclipse.jface.text.rules.ICharacterScanner)
	 */
	protected void unreadBuffer(ICharacterScanner scanner) {
		for (int i= fBuffer.length() - 1; i >= 0; i--)
			scanner.unread();
	}
}
