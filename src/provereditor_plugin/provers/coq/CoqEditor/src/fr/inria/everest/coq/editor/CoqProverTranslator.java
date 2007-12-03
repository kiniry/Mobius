package fr.inria.everest.coq.editor;

import java.io.InputStream;
import java.util.regex.Pattern;

import mobius.prover.plugins.AProverTranslator;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IWordDetector;
import org.eclipse.jface.text.rules.MultiLineRule;
import org.eclipse.jface.text.rules.SingleLineRule;
import org.eclipse.jface.text.rules.WordRule;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.PlatformUI;

import prover.gui.editor.FixedSizeWordRule;
import prover.gui.editor.ProverEditor;
import prover.gui.editor.detector.ExprDetector;
import prover.gui.editor.detector.WordDetector;
import prover.gui.editor.outline.types.ProverType;
import fr.inria.everest.coq.editor.utils.CoqConstructFinder;
import fr.inria.everest.coq.editor.utils.ICoqColorConstants;

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
		{"([0-9]+) subgoals", "\n\n\\Subgoals :"},
		{"([0-9]+) subgoal", "\n\n\\Subgoal :"},
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
	public IRule [] getProverTheoryRules() {
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
		SingleLineRule subg = new SingleLineRule("Subgoal", ":", completed);
		subg.setColumnConstraint(0);
		MultiLineRule mlr = new MultiLineRule("subgoal", "",subgoal2, (char) 0, true);
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
	public IRule [] getProverStateRules() {				
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
		return s.matches("Error.*") || s.matches("Invalid module name.*");
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
		if(path == null)
			path = new String[0];
		String [] cmds = new String[1 + (path.length * 2) + 1];
		cmds[0] = ide;
		for(int i = 0; i < path.length; i++) {
			cmds[(i * 2) + 1] = "-I";
			cmds[(i * 2) + 2] = path[i];
		}
		//cmds[cmds.length - 2] = "-compile";
		cmds[cmds.length - 1] = file.substring(0, file.length() -2);
		return cmds;
	}

	
	public static Image [] imgs;
	public Image createImage(String path) {
		InputStream is = this.getClass().getClassLoader().getResourceAsStream(path);
		Image img = new Image(PlatformUI.getWorkbench().getDisplay(), is);
		return img;
	}
	
	public ProverType getFileOutline(ProverEditor ed, IDocument doc, ProverType root) {

		if(imgs == null) {
			Image [] tab = { createImage("/icons/module.gif"),
					createImage("/icons/moduleb.gif"),
					createImage("/icons/sections.gif"),
					createImage("/icons/defs1.gif"),
					createImage("/icons/defs2.gif"),
					createImage("/icons/defs3.gif"),
					createImage("/icons/defs4.gif"),
					createImage("/icons/defs5.gif"),
					createImage("/icons/defs6.gif"),
					createImage("/icons/defs7.gif"),
					createImage("/icons/defs8.gif")};
			imgs = tab;
		}
		CoqConstructFinder ccf = new CoqConstructFinder(ed, doc);
		
		ccf.parse(root);
		return root;
	}
	
	private final static Pattern [] [] pats = {
		{Pattern.compile("\\s*Module Type\\s*"), Pattern.compile("[a-zA-Z_0-9]*")},
		{Pattern.compile("\\s*Module\\s*"), Pattern.compile("[a-zA-Z_0-9]*")},
		{Pattern.compile("\\s*Definition\\s*"), Pattern.compile("[a-zA-Z_0-9]*")},
		{Pattern.compile("\\s*Lemma\\s*"), Pattern.compile("[a-zA-Z_0-9]*")},
		{Pattern.compile("\\s*Fixpoint\\s*"), Pattern.compile("[a-zA-Z_0-9]*")},
		{Pattern.compile("\\s*Axiom\\s*"), Pattern.compile("[a-zA-Z_0-9]*")},
		{Pattern.compile("\\s*Parameter\\s*"), Pattern.compile("[a-zA-Z_0-9]*")},
		{Pattern.compile("\\s*Inductive\\s*"), Pattern.compile("[a-zA-Z_0-9]*")},
		{Pattern.compile("\\s*Variable\\s*"), Pattern.compile("[a-zA-Z_0-9]*")},
		};
	public Pattern [][] getTagPatterns() {
		return pats;
	}

}
