package fr.inria.everest.coq.editor;

import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IWordDetector;
import org.eclipse.jface.text.rules.MultiLineRule;
import org.eclipse.jface.text.rules.SingleLineRule;
import org.eclipse.jface.text.rules.WordRule;

import prover.AProverTranslator;
import prover.Prover;
import prover.ProverEditorPlugin;
import prover.exec.AProverException;
import prover.exec.ITopLevel;
import prover.gui.editor.FixedSizeWordRule;
import prover.gui.editor.detector.ExprDetector;
import prover.gui.editor.detector.WordDetector;

public class CoqProverTranslator extends AProverTranslator implements ICoqColorConstants {
	
	public final static CoqProverTranslator instance = new CoqProverTranslator();
	public final static String [] vernac = {"forall", "Proof",
			"Load", "Require", "Qed", "Import", "Open", "Scope", 
			"match","end", "Section", "End" 
	};
	public final static String [] lem = {
			"Definition", "Variable", "Lemma", "Fixpoint", "Axiom", "Hypothesis", "Inductive"
	};
				
	public final static String [] errorExpressions = { 
		"Error:", "Anomaly:", "Toplevel input",
		"User error", "Syntax error: "
	};
	public final static String [][] replacements = {
		{"\ufffd", " "},
		{"============================",
			"-----------------------------------------------------------------------------------"
		}
    };	
	
	

	private IRule [] proofRules;
	private IRule [] fileRules;
	private IRule [] parsingRules;
	
	public String[] getErrorExpressions() {
		return errorExpressions;
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
		Prover po = ProverEditorPlugin.getInstance().getProver("Coq"); 
		cmds[0] = po.getTop();
		cmds[cmds.length - 1] = "-emacs";
		return new BasicCoqTop(cmds, po.getGraceTime());
	}

	
	public String [][] getReplacements() {
		return replacements;
	}

	private IRule [] initFileRules() {
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
		if(fileRules == null)
			fileRules = initFileRules();
		return fileRules;
	}
	
	private IRule [] initProofRules() {
		WordRule wr = new WordRule(new WordDetector(), def);
		for (int i = 0; i < vernac.length; i++) {
			wr.addWord(vernac[i], tag);
		}
		for (int i = 0; i < lem.length; i++) {
			wr.addWord(lem[i], lemma);
		}
		WordRule wexpr = new WordRule(new ExprDetector(), tag);
		wexpr.addWord(".", tag);
		WordRule hypothesis = new WordRule(new WordDetector(), comment);
		hypothesis.setColumnConstraint(2);
//		WordPatternRule hypothesis = new WordPatternRule(new WordDetector(), "  ", " :", comment);
//		hypothesis.setColumnConstraint(0);
		SingleLineRule subg = new SingleLineRule("1 ", "subgoal", completed);
		subg.setColumnConstraint(0);
		MultiLineRule mlr = new MultiLineRule(" subgoal", "",subgoal2, (char) 0, true);
		mlr.setColumnConstraint(0);
		IRule [] rules = {
				new SingleLineRule("Proof ", "completed", completed),
				subg, mlr, hypothesis,
				new MultiLineRule("forall ", ",", forall),
				new MultiLineRule("exists ", ",", forall),
				new MultiLineRule("(*", "*)", comment),
				new MultiLineRule("\"", "\"", string),
				new SingleLineRule("(*", "*)", comment),
				new SingleLineRule("\"", "\"", string),
				wr, wexpr};
		return rules;
	}
	
	public IRule [] getProofRules() {				
		if(proofRules == null)
			proofRules = initProofRules();
		return proofRules;
	}

	private IRule[] initParsingRules() {
		WordRule endofsentence = new FixedSizeWordRule(new IWordDetector() {

			public boolean isWordStart(char c) {
				return c == '.';
			}

			public boolean isWordPart(char c) {
				return Character.isWhitespace(c);
			}
			
		}, 2);

		endofsentence.addWord(". ", SENTENCE_TOKEN);
		endofsentence.addWord(".\n", SENTENCE_TOKEN);
		endofsentence.addWord(".\t", SENTENCE_TOKEN);
		
		IRule [] rules = {
			new MultiLineRule("(*", "*)", COMMENT_TOKEN),
			new MultiLineRule("\"", "\"", COMMENT_TOKEN),

			new SingleLineRule("(*", "*)", COMMENT_TOKEN),
			new SingleLineRule("\"", "\"", COMMENT_TOKEN),
			endofsentence
		};
		return rules;
	}
	public IRule[] getParsingRules() {
		if(parsingRules == null) {
			parsingRules = initParsingRules();
		}
		return parsingRules;
	}


	public boolean isErrorMsg(String s) {
		return s.matches("Error.*");
	}
}
