package prover;

import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.Token;

import prover.exec.AProverException;
import prover.exec.ITopLevel;

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
	
	public String [][] getUnicodeReplacements() {
		return unicodeReplacements;
	}
	
	public String [][] getReplacements() {
		return replacements;
	}
//	public abstract String[] getErrorExpressions();

	public abstract ITopLevel createNewTopLevel(String[] paths) throws AProverException;
	
    public abstract IRule [] getProofRules();
	public abstract IRule [] getFileRules();
	public abstract IRule [] getParsingRules();

	public abstract boolean isErrorMsg(String s);
}
