package prover;

import prover.exec.AProverException;
import prover.exec.ITopLevel;

public abstract class AProverTranslator {
	public static String [][] unicodeReplacement = {
		{"<->", "\u2194"},
		{"->", "\u2192"},
		{"exists", "\u2203"},
		{"\\\\/", "\u2228"},
		{"/\\\\", "\u2227"}
    };
	public String [][] getUnicodeReplacement() {
		return unicodeReplacement;
	}
	
	public abstract String[] getErrorExpressions();
	public abstract String getCommentBegin();
	public abstract String getCommentEnd();
	public abstract String getEndOfSentence();
	public abstract ITopLevel createNewTopLevel(String[] paths) throws AProverException;
}
