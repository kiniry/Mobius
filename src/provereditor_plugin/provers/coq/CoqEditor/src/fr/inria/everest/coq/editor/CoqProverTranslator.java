package fr.inria.everest.coq.editor;

import prover.AProverTranslator;
import prover.exec.ITopLevel;
import prover.exec.toplevel.exceptions.CoqException;
import fr.inria.everest.coq.CoqUtils;
import fr.inria.everest.coq.coqtop.CoqTop;

public class CoqProverTranslator extends AProverTranslator {
	
	public final static String strCommentBegin = "\\(\\*";
	public final static String strCommentEnd = "\\*\\)";
	public final static String strEndOfSentence = "\\.[ \n\t]"; 
	public final static CoqProverTranslator instance = new CoqProverTranslator();
	
	public final static String [] errorExpressions = { 
		"Error:", "Anomaly:", "Toplevel input",
		"User error", "Syntax error: "
	};
	
	public ITopLevel createNewTopLevel(String[] paths) throws CoqException {
		return new CoqTop(CoqUtils.getCoqTop(), paths);
	}
	
	public String[] getErrorExpressions() {
		return errorExpressions;
	}
	
	public String getCommentBegin() {
		return strCommentBegin;
	}
	
	public String getCommentEnd() {
		return strCommentEnd;
	}
	
	public String getEndOfSentence() {
		return strEndOfSentence;
	}
	
	public static AProverTranslator getInstance() {
		return instance;
	}
}
