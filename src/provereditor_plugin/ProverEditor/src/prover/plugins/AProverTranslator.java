package prover.plugins;

import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.Token;

/**
 * This class is the main class to implement by a plugin
 * extending the <code>prover.editor</code> extension point.
 * It offers all the translations/specific things for the gui
 * of a prover plugin in ProverEditor.
 * @author J. Charles
 */
public abstract class AProverTranslator {
	/** a token to return by a rule when encountering a comment while parsing */
	public static final IToken COMMENT_TOKEN = new Token("comment");
	/** a token to return by a rule when encountering the end of a command while parsing */
	public static final IToken SENTENCE_TOKEN = new Token("sentence");
	
	/** some basic unicode replacements */
	private final static String [][] unicodeReplacements = {
		{"<->", "\u2194"},
		{"->", "\u2192"},
		{"exists", "\u2203"},
		{"\\\\/", "\u2228"},
		{"/\\\\", "\u2227"}
    };
	/** basic replacements: no replacements */
	private final static String [][] replacements = {};
	
	
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

	/**
	 * Returns the array of rules used to highlight the proof.
	 * @return an array of rules, can be empty but not <code>null</code>
	 */
    public abstract IRule [] getProofRules();
    
	/**
	 * Returns the array of rules used to highlight the file in the 
	 * prover language.
	 * @return an array of rules, can be empty but not <code>null</code>
	 */
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

	/**
	 * Tells if the specified message is an error. This method
	 * is an oracle used while compiling a file, to know if the 
	 * compilation was a success.
	 * @param s the message to understand
	 * @return <code>true</code> if no errors were found
	 */
	public abstract boolean isErrorMsg(String s);
	
	/**
	 * Compute the ide command, from the ide path
	 * the path to its libraries, and the file to edit in the
	 * ide.
	 * @param ide the ide path as specified by the user in the
	 * preference page.
	 * @param path the different library paths gotten from the environment
	 * @param file the full path to the file to open
	 * @return an array containing the command line 
	 * as specified for {@link java.lang.Runtime#exec(java.lang.String[])}
	 */
	public abstract String[] getIdeCommand(String ide, String[] path, String file);
	
	/**
	 * Compute the compiling command, from the compiler path
	 * the path to the libraries, and the path to the file to compile.
	 * @param comp the compiler path as specified by the user in the
	 * preference page.
	 * @param path the different library paths gotten from the environment
	 * @param file the full path to the file to compile
	 * @return an array containing the command line 
	 * as specified for {@link java.lang.Runtime#exec(java.lang.String[])}
	 */
	public abstract String[] getCompilingCommand(String comp, String[] path, String file);
}
