package fr.inria.everest.coq.editor;

import prover.AProverTranslator;
import prover.exec.AProverException;
import prover.exec.ITopLevel;
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
	
	
	public ITopLevel createNewTopLevel(String[] path) throws AProverException {
		String [] cmds;
		if(path != null) {
			cmds = new String[2 + path.length * 2];
			for(int i = 0; i < path.length; i++) {
				cmds[(2 * i) + 1] = "-I";
				cmds[(2 * i) + 2] = path[i];
			}
			
		}
		else {
			cmds = new String[2];
		}
		cmds[0] = CoqUtils.getCoqTop().trim();
		cmds[cmds.length - 1] = "-emacs";
		return new CoqTop(cmds, 10);
	}
}
