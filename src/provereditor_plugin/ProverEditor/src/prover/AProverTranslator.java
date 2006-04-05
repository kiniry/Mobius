package prover;

import org.eclipse.jface.text.rules.IRule;

import prover.exec.AProverException;
import prover.exec.ITopLevel;

public abstract class AProverTranslator {
	public static String [][] unicodeReplacements = {
		{"<->", "\u2194"},
		{"->", "\u2192"},
		{"exists", "\u2203"},
		{"\\\\/", "\u2228"},
		{"/\\\\", "\u2227"}
    };
	public static String [][] replacements = {};
	
	public String [][] getUnicodeReplacements() {
		return unicodeReplacements;
	}
	
	public String [][] getReplacements() {
		return replacements;
	}
	public abstract String[] getErrorExpressions();
	public abstract String getCommentBegin();
	public abstract String getCommentEnd();
	public abstract String getEndOfSentence();
	public abstract ITopLevel createNewTopLevel(String[] paths) throws AProverException;
	
    public abstract IRule [] getProofRules();
	public abstract IRule [] getFileRules();
}
