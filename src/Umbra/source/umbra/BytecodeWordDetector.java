/*
 * Created on 2005-04-25
 *
 */
package umbra;

import org.eclipse.jface.text.rules.IWordDetector;

/**
 * @author Wojtek W¹s
 */
public class BytecodeWordDetector implements IWordDetector {

	public boolean isWordStart(char c) {
		return Character.isLetter(c);
	}

	public boolean isWordPart(char c) {
		return (Character.isLetterOrDigit(c) || c == '_');
	}
}
