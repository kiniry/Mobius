package ie.ucd.bon.plugin.editor;

import org.eclipse.jface.text.rules.IWordDetector;

public class BONWordDector implements IWordDetector {

	public boolean isWordPart(char c) {
		return isBONWordChar(c);
	}

	public boolean isWordStart(char c) {
		return isBONWordChar(c);
	}
	
	private boolean isBONWordChar(char c) {
		return Character.isLetterOrDigit(c) || c == '_'; 
	}

}
