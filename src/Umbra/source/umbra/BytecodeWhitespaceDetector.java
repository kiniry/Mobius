package umbra;

import org.eclipse.jface.text.rules.IWhitespaceDetector;

/**
 * New definition of whitespace
 * 
 * @author Wojciech W¹s
 */

public class BytecodeWhitespaceDetector implements IWhitespaceDetector {

	public boolean isWhitespace(char c) {
		return (c == ' ' || c == '\t' || c == '\n' || c == '\r');
	}
}
