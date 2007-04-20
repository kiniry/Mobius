/*
 * Created on 2005-04-25
 *
 */
package umbra.editor.parsing;

import org.eclipse.jface.text.rules.IWordDetector;

/**
 * TODO
 * 
 * @author Wojtek Wąs
 */
public class BytecodeWordDetector implements IWordDetector {

	/**
	 * TODO
	 */
	public boolean isWordStart(char c) {
		return Character.isLetter(c);
	}

	/**
	 * TODO
	 */
	public boolean isWordPart(char c) {
		return (Character.isLetterOrDigit(c) || c == '_');
	}
}
