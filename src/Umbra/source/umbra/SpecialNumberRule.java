/*
 * Created on 2005-05-13
 */
package umbra;

import org.eclipse.jface.text.rules.ICharacterScanner;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.NumberRule;
import org.eclipse.jface.text.rules.Token;

/**
 * Modified NumberRule that allows an additional mark before
 * (or after) the number to be read (used with '#' and '%').
 * 
 * @author Wojtek W�s
 */
public class SpecialNumberRule extends NumberRule {

    /**
     * TODO write description
     */
    char start;
    /**
     * TODO write description
     */
    char fin;
    /**
     * TODO write description
     */
    boolean isFin;
	
    /**
     * TODO write description
     * 
     * @param start TODO write description
     * @param fin TODO write description
     * @param token TODO write description
     */
    public SpecialNumberRule(char start, char fin, IToken token) {
		super(token);
		this.start = start;
		this.fin = fin;
		isFin = true;
	}
	
    /**
     * TODO write description
     * 
     * @param start TODO write description
     * @param token TODO write description
     */
    public SpecialNumberRule(char start, IToken token) {
		super(token);
		this.start = start;
		isFin = false;
	}

    /**
     * TODO write description
     * 
     * @param scanner TODO write description
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
