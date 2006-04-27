package prover.plugins;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.Token;

import prover.gui.editor.outline.types.ProverType;

/**
 * This class is the main class to implement by a plugin
 * extending the <code>prover.editor</code> extension point.
 * It offers all the translations/specific things for the gui
 * of a prover plugin in ProverEditor.
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
	 * Returns an array consisting of a set of pairs, where \result[i][0] is paired with 
   * \result[i][1], where each \result[i][0] is a string and \result[i][1] is its Unicode 
   * replacement.  This replacement set is only used when the Prover Editor proferences option 
   * "Use unicode characters" is selected.
	 * @return What is the array of substitution pairs, as specified above?
   * @see #getReplacements()
	 */
	public /*@ non_null @*/ String [][] getUnicodeReplacements() {
		return unicodeReplacements;
	}
	
	/**
   * Returns an array consisting of a set of pairs, where \result[i][0] is paired with 
   * \result[i][1], where each \result[i][0] is a regexp string and \result[i][1] is its 
   * string replacement.  Substitution is performed via 
   * {@link java.lang.String#replaceAll(java.lang.String, java.lang.String)}.
   * @return What is the array of substitution pairs, as specified above?
   * @see #getUnicodeReplacements()
	 */
	public /*@ non_null @*/ String [][] getReplacements() {
		return replacements;
	}

	/**
   * @return What is the array of {@link IRule}s that may be used to highlight the top-level 
   * state and/or proof-state in the Prover Editor Toplevel view?
	 */
  public abstract /*@ non_null @*/ IRule [] getProofRules();
    
	/**
   * @return What is the array of {@link IRule}s that may be used to highlight the theory
   * specification/proof script file (in the language of the prover; e.g., a .v file in Coq)?
	 */
	public abstract IRule /*@ non_null @*/ [] getFileRules();
	
	/**
	 * @return What is the array of {@link IRule}s that may be used to highlight the portions of
   * the theory specification/proof script file as we progress within the evaluation of the
   * file's contents.  E.g., in Coq, these rules matches comments and sentences that end in
   * '.' followed by whitespace (i.e., a newline, because the other periods are used for
   * namespaces or elipses to trigger automatic tactic application).  If the returned tag from 
   * a rule is {@link #SENTENCE_TOKEN}, then end of sentence has been detected.
	 */
	public abstract IRule /*@ non_null @*/ [] getParsingRules();

	/**
	 * @param s the message to evalute.
	 * @return Is the string <var>s</var> an error message returned by the compiler?
	 */
	public abstract boolean isErrorMsg(String s);
	
	/**
	 * Compute the command to run the "normal" prover interface (e.g., Emacs with Coq or PVS), 
   * from the IDE path, the path to its libraries, and the file to edit in the IDE.  You use
   * this command when you have become completely frustrated by the Eclipse front-end.
   * Typically, this command is trigger from by ProverEditor->LaunchIDE file menu.
	 * @param ide the IDE path as specified by the user in the preference page.
   * @param path a sequence of fully resolved paths, the first element of which is where the
   * prover should run, and the other paths are library paths from the environment.  Your
   * prover may choose to ignore the running location specified in path[0] as Coq does.
   * @param file the full path to the file to compile.
   * @return What is the command-line that may be used with 
   * {@link java.lang.Runtime#exec(java.lang.String[])} that will cause <var>file</var> to be
   * loaded into the "normal" IDE for this prover, as specified in the project preferences?
	 */
	public abstract String[] /*@ non_null @*/ getIdeCommand(String ide, String[] path, String file);
	
	/**
	 * Compute the "compiling" command, (the command to execute that will cause the prover to
   * compile <var>file</var>) from the compiler path, the path to the libraries, and the path 
   * to the file to compile.
   * Typically, this command is trigger from by ProverEditor->Compile file menu.
	 * @param comp the top-level path to the compiler executable or wrapper shell script, as 
   * specified by the user in the preference page.
   * @param path a sequence of fully resolved paths, the first element of which is where the
   * prover should run, and the other paths are library paths from the environment.  Your
   * prover may choose to ignore the running location specified in path[0] as Coq does.
   * @param file the full path to the file to compile.
   * @return What is the command-line that may be used with 
   * {@link java.lang.Runtime#exec(java.lang.String[])} that will cause <var>file</var> to be
   * compiled?
	 */
	public abstract /*@ non_null @*/ String[] getCompilingCommand(String comp, String[] path, String file);

	
	
	/**
	 * Experimental -- do not user
	 * @param doc
	 * @param root
	 * @return
	 */
	public ProverType getFileOutline(IDocument doc, ProverType root) {
		return root;
	}

}
