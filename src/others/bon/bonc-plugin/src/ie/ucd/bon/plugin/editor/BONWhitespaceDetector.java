package ie.ucd.bon.plugin.editor;


import org.eclipse.jface.text.rules.IWhitespaceDetector;

public class BONWhitespaceDetector implements IWhitespaceDetector {

	public boolean isWhitespace(char character) {
		return Character.isWhitespace(character);
	}
}
