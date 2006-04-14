package prover.plugins;

import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.Token;


public abstract class AProverTranslator {
	private final static String [][] unicodeReplacements = {
		{"<->", "\u2194"},
		{"->", "\u2192"},
		{"exists", "\u2203"},
		{"\\\\/", "\u2228"},
		{"/\\\\", "\u2227"}
    };
	private final static String [][] replacements = {};
	
	
	public static final IToken COMMENT_TOKEN = new Token("comment");
	public static final IToken SENTENCE_TOKEN = new Token("sentence");
	
	
	/**
	 * Returns an array consisting of couples a 
	 * string / its unicode replacement.
	 * Used when the option "Use unicode characters" is
	 * selected.
	 * @return An array of couples (it can be empty), not null.
	 */
	public String [][] getUnicodeReplacements() {
		return unicodeReplacements;
	}
	
	
	/**
	 * Returns an array consisting of couples:
	 * String and its replacement.
	 * @return an array of replacements. The array can be empty,
	 * not <code>null</code>.
	 */
	public String [][] getReplacements() {
		return replacements;
	}

    public abstract IRule [] getProofRules();
	public abstract IRule [] getFileRules();
	
	/**
	 * Returns a serie of rules used to parse
	 * the sentences from the file. If 
	 * the returned tag from the rule is {@link #SENTENCE_TOKEN}
	 * it is considered that an end of sentence has been detected.
	 * A command can be sent.
	 * @return Rules to parse the input to send to the prover from a file
	 */
	public abstract IRule [] getParsingRules();

	public abstract boolean isErrorMsg(String s);
	
	public abstract String[] getIdeCommand(String ide, String[] path, String file);
	public abstract String[] getCompilingCommand(String ide, String[] path, String file);
}
