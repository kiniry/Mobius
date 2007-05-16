package umbra.editor.parsing;

import org.eclipse.jface.text.rules.IWhitespaceDetector;

/**
 * New definition of whitespace
 * 
 * @author Wojciech Wąs
 */
public class BytecodeWhitespaceDetector implements IWhitespaceDetector {

	/**
	 * This method defines which characters are whitespace characters
	 * 
	 * @param c the character to determine if it is whitespace
	 */
	public boolean isWhitespace(char c) {
		return (c == ' ' || c == '\t' || c == '\n' || c == '\r');
	}
}
