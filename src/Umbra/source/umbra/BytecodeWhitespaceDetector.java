package umbra;

import org.eclipse.jface.text.rules.IWhitespaceDetector;

/**
 * New definition of whitespace
 * 
 * @author Wojciech W�s
 */

public class BytecodeWhitespaceDetector implements IWhitespaceDetector {

    /**
     * TODO write description
     * 
     * @param c TODO write description
     */
    public boolean isWhitespace(char c) {
		return (c == ' ' || c == '\t' || c == '\n' || c == '\r');
	}
}
