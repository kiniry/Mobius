package fr.inria.everest.coq.editor;

import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IWordDetector;
import org.eclipse.jface.text.rules.MultiLineRule;
import org.eclipse.jface.text.rules.SingleLineRule;
import org.eclipse.jface.text.rules.WordRule;

import prover.gui.editor.FixedSizeWordRule;
import prover.gui.editor.detector.ExprDetector;
import prover.gui.editor.detector.WordDetector;
import prover.plugins.AProverTranslator;

public class CoqProverTranslator extends AProverTranslator implements ICoqColorConstants {
	
	public final static CoqProverTranslator instance = new CoqProverTranslator();
	public final static String [] vernac = {"forall", "Proof",
			"Load", "Require", "Qed", "Import", "Open", "Scope", 
			"match","end", "Section", "End" 
	};
	public final static String [] lem = {
			"Definition", "Variable", "Lemma", "Fixpoint", "Axiom", "Hypothesis", "Inductive"
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

	
	
	public static AProverTranslator getInstance() {
		return instance;
	}
	
	/*
	 *  (non-Javadoc)
	 * @see prover.plugins.AProverTranslator#getReplacements()
	 */
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
	/*
	 *  (non-Javadoc)
	 * @see prover.plugins.AProverTranslator#getFileRules()
	 */
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
	
	/*
	 *  (non-Javadoc)
	 * @see prover.plugins.AProverTranslator#getProofRules()
	 */
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

	/*
	 *  (non-Javadoc)
	 * @see prover.plugins.AProverTranslator#getParsingRules()
	 */
	public IRule[] getParsingRules() {
		if(parsingRules == null) {
			parsingRules = initParsingRules();
		}
		return parsingRules;
	}

	/*
	 *  (non-Javadoc)
	 * @see prover.plugins.AProverTranslator#isErrorMsg(java.lang.String)
	 */
	public boolean isErrorMsg(String s) {
		return s.matches("Error.*");
	}


	/*
	 *  (non-Javadoc)
	 * @see prover.plugins.AProverTranslator#getIdeCommand(java.lang.String, java.lang.String[], java.lang.String)
	 */
	public String[] getIdeCommand(String ide, String[] path, String file) {
		String [] cmds = new String[1 + (path.length * 2) + 1];
		cmds[0] = ide;
		for(int i = 0; i < path.length; i++) {
			cmds[(i * 2) + 1] = "-I";
			cmds[(i * 2) + 2] = path[i];
		}
		cmds[cmds.length - 1] = file;
		return cmds;
	}

	/*
	 *  (non-Javadoc)
	 * @see prover.plugins.AProverTranslator#getCompilingCommand(java.lang.String, java.lang.String[], java.lang.String)
	 */
	public String[] getCompilingCommand(String ide, String[] path, String file) {
		String [] cmds = new String[1 + (path.length * 2) + 2];
		cmds[0] = ide;
		for(int i = 0; i < path.length; i++) {
			cmds[(i * 2) + 1] = "-I";
			cmds[(i * 2) + 2] = path[i];
		}
		cmds[cmds.length - 2] = "-compile";
		cmds[cmds.length - 1] = file.substring(0, file.length() -2);
		return cmds;
	}

}
