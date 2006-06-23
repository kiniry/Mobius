/*
 * Created on 2005-04-25
 *
 */
package umbra;

import org.eclipse.jface.text.rules.IWordDetector;

/**
 * TODO write description
 * 
 * @author Wojtek W�s
 */
public class BytecodeWordDetector implements IWordDetector {

    /**
     * TODO write description
     * 
     * @param c TODO write description
     */
    public boolean isWordStart(char c) {
		return Character.isLetter(c);
	}

    /**
     * TODO write description
     * 
     * @param c TODO write description
     */
    public boolean isWordPart(char c) {
		return (Character.isLetterOrDigit(c) || c == '_');
	}
}
