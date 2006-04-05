package fr.inria.everest.coq.editor;

import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.MultiLineRule;
import org.eclipse.jface.text.rules.SingleLineRule;
import org.eclipse.jface.text.rules.WordRule;

import prover.AProverTranslator;
import prover.exec.AProverException;
import prover.exec.ITopLevel;
import prover.gui.editor.detector.ExprDetector;
import prover.gui.editor.detector.WordDetector;
import fr.inria.everest.coq.CoqUtils;
import fr.inria.everest.coq.coqtop.CoqTop;

public class CoqProverTranslator extends AProverTranslator implements ICoqColorConstants {
	
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
	public static String [][] replacements = {
		{"\ufffd", " "},
		{"============================",
			"-----------------------------------------------------------------------------------"
		}
    };
	
	public String [][] getReplacements() {
		return replacements;
	}

	public IRule [] getProofRules() {
		String [] vernac = {"forall", "Proof",
				"Load", "Require", "Qed", "Import", "Open", "Scope", 
				"match","end", "Section", "End" 
		};
		String [] lem = {
				"Definition", "Variable", "Lemma", "Fixpoint", "Axiom", "Hypothesis", "Inductive"
		};
				
		WordRule wr = new WordRule(new WordDetector(), def);
		for (int i = 0; i < vernac.length; i++) {
			wr.addWord(vernac[i], tag);
		}
		for (int i = 0; i < lem.length; i++) {
			wr.addWord(lem[i], lemma);
		}
		WordRule wexpr = new WordRule(new ExprDetector(), tag);
		wexpr.addWord(".", tag);
		IRule [] rules = {
				new SingleLineRule("Proof ", "completed", completed),
				new MultiLineRule("forall ", ",", forall),
				new MultiLineRule("exists ", ",", forall),
				new MultiLineRule("(*", "*)", comment),
				new MultiLineRule("\"", "\"", string),
				new SingleLineRule("(*", "*)", comment),
				new SingleLineRule("\"", "\"", string),
				wr,
				wexpr
				
		};
		return rules;
	}
	
	public IRule [] getFileRules() {
		String [] vernac = {"forall", "Proof",
				"Load", "Require", "Qed", "Import", "Open", "Scope", 
				"match","end", "Section", "End" 
		};
		String [] lem = {
				"Definition", "Variable", "Lemma", "Fixpoint", "Axiom", "Hypothesis", "Inductive"
		};
				
		WordRule wr = new WordRule(new WordDetector(), def);
		for (int i = 0; i < vernac.length; i++) {
			wr.addWord(vernac[i], tag);
		}
		for (int i = 0; i < lem.length; i++) {
			wr.addWord(lem[i], lemma);
		}
		WordRule wexpr = new WordRule(new ExprDetector(), tag);
		wexpr.addWord(".", tag);
		IRule [] rules = {
				new SingleLineRule("Proof ", "completed", completed),
				new MultiLineRule("forall ", ",", forall),
				new MultiLineRule("exists ", ",", forall),
				new MultiLineRule("(*", "*)", comment),
				new MultiLineRule("\"", "\"", string),
				new SingleLineRule("(*", "*)", comment),
				new SingleLineRule("\"", "\"", string),
				wr,
				wexpr
				
		};
		return rules;
	}
}
