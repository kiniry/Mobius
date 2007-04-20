/*
 * Created on 2005-05-13
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
 * @author Wojtek Wąs
 */
public class SpecialNumberRule extends NumberRule {

	/**
	 * TODO
	 */
	char start;
	/**
	 * TODO
	 */
	char fin;
	/**
	 * TODO
	 */
	boolean isFin;
	
	/**
	 * TODO
	 */
	public SpecialNumberRule(char start, char fin, IToken token) {
		super(token);
		this.start = start;
		this.fin = fin;
		isFin = true;
	}
	
	/**
	 * TODO
	 */
	public SpecialNumberRule(char start, IToken token) {
		super(token);
		this.start = start;
		isFin = false;
	}

	/**
	 * TODO
	 */
	public IToken evaluate(ICharacterScanner scanner) {
		int c= scanner.read();
		if ((char)c == start) {
			if (super.evaluate(scanner) == fToken) {
				if (!isFin) return fToken;
				c = scanner.read();
				if ((char)c == fin) return fToken;
				do {
					scanner.unread();
					scanner.unread();
					c = scanner.read();
				} while (Character.isDigit((char) c));
			}
		}
		scanner.unread();
		return Token.UNDEFINED;
	}
}
