/*
 * Created on Dec 8, 2004
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package jack.plugin.edit;

import java.util.Hashtable;

/**
 *
 *  @author L. Burdy
 **/
/**
 * A simple scanner for Java and JML
 */
public class JavaScanner {

	protected Hashtable fgKeys = null;
	protected StringBuffer fBuffer = new StringBuffer();
	protected String fDoc;
	protected int fPos;
	protected int fEnd;
	protected int fStartToken;
	protected boolean fEofSeen = false;

	private String[] fgKeywords = {"abstract", "boolean", "break", "byte", "case", "catch", "char", "class",
			"continue", "default", "do", "double", "else", "extends", "false", "final", "finally", "float", "for",
			"if", "implements", "import", "instanceof", "int", "interface", "long", "native", "new", "null", "package",
			"private", "protected", "public", "return", "short", "static", "super", "switch", "synchronized", "this",
			"throw", "throws", "transient", "true", "try", "void", "volatile", "while"};

	protected String[] fgKeywordsJml = {"requires", "modifies", "assignable", "ensures", "exsures", "signals",
			"invariant", "loop_modifies", "loop_invariant"};

	public JavaScanner() {
		initialize();
	}

	public String[] getFgKeywords() {
		return fgKeywords;
	}
	/**
	 * Returns the ending location of the current token in the document.
	 */
	public final int getLength() {
		return fPos - fStartToken;
	}

	/**
	 * Initialize the lookup table.
	 */
	void initialize() {
		fgKeys = new Hashtable();
		Integer k = new Integer(JavaLineStyler.KEY);
		for (int i = 0; i < getFgKeywords().length; i++)
			fgKeys.put(getFgKeywords()[i], k);
		k = new Integer(JavaLineStyler.KEY_JML);
		for (int i = 0; i < fgKeywordsJml.length; i++)
			fgKeys.put(fgKeywordsJml[i], k);
	}

	/**
	 * Returns the starting location of the current token in the document.
	 */
	public final int getStartOffset() {
		return fStartToken;
	}

	/**
	 * Returns the next lexical token in the document.
	 */
	public int nextToken() {
		int c, result;
		fStartToken = fPos;
		while (true) {
			switch (c = read()) {
				case JavaLineStyler.EOF :
					return JavaLineStyler.EOF;
				case '/' : // comment
					c = read();
					if (c == '/') {
						c = read();
						if (c == '@') {
							unread(c);
							unread(c);
							return JavaLineStyler.OTHER;
							//	result = SINGLE_COMMENT_JML;
						} else
							result = JavaLineStyler.SINGLE_COMMENT;
						while (true) {
							c = read();
							if ((c == JavaLineStyler.EOF) || (c == JavaLineStyler.EOL)) {
								unread(c);
								return result;
							}
						}
					} else {
						unread(c);
					}
					return JavaLineStyler.OTHER;
				case '\'' : // char const
					character : for (;;) {
						c = read();
						switch (c) {
							case '\'' :
								return JavaLineStyler.STRING;
							case JavaLineStyler.EOF :
								unread(c);
								return JavaLineStyler.STRING;
							case '\\' :
								c = read();
								break;
						}
					}

				case '"' : // string
					string : for (;;) {
						c = read();
						switch (c) {
							case '"' :
								return JavaLineStyler.STRING;
							case JavaLineStyler.EOF :
								unread(c);
								return JavaLineStyler.STRING;
							case '\\' :
								c = read();
								break;
						}
					}

				case '0' :
				case '1' :
				case '2' :
				case '3' :
				case '4' :
				case '5' :
				case '6' :
				case '7' :
				case '8' :
				case '9' :
					do {
						c = read();
					} while (Character.isDigit((char) c));
					unread(c);
					return JavaLineStyler.NUMBER;
				default :
					if (Character.isWhitespace((char) c)) {
						do {
							c = read();
						} while (Character.isWhitespace((char) c));
						unread(c);
						return JavaLineStyler.WHITE;
					}
					if (Character.isJavaIdentifierStart((char) c)) {
						fBuffer.setLength(0);
						do {
							fBuffer.append((char) c);
							c = read();
						} while (Character.isJavaIdentifierPart((char) c));
						unread(c);
						Integer i = (Integer) fgKeys.get(fBuffer.toString());
						if (i != null)
							return i.intValue();
						return JavaLineStyler.WORD;
					}
					return JavaLineStyler.OTHER;
			}
		}
	}

	/**
	 * Returns next character.
	 */
	protected int read() {
		if (fPos <= fEnd) {
			return fDoc.charAt(fPos++);
		}
		return JavaLineStyler.EOF;
	}

	public void setRange(String text) {
		fDoc = text;
		fPos = 0;
		fEnd = fDoc.length() - 1;
	}

	protected void unread(int c) {
		if (c != JavaLineStyler.EOF)
			fPos--;
	}
}

