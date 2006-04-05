package fr.inria.everest.coq.editor;

import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.MultiLineRule;
import org.eclipse.jface.text.rules.SingleLineRule;
import org.eclipse.jface.text.rules.Token;
import org.eclipse.jface.text.rules.WordRule;


import prover.gui.editor.BasicRuleScanner;
import prover.gui.editor.BasicTextAttribute;
import prover.gui.editor.detector.ExprDetector;
import prover.gui.editor.detector.WordDetector;

public class CoqRuleScanner extends BasicRuleScanner implements ICoqColorConstants {
	
	public CoqRuleScanner() {
		super();
		String [] vernac = {
				"Load", "Require", "Proof", "Qed", "Import", "Open", "Scope", 
				"match","end", "Section", "End" 
		};
		String [] lem = {
				"Definition", "Variable", "Lemma", "Fixpoint", "Axiom", "Hypothesis", "Inductive"
		};
		IToken tag = new Token(new BasicTextAttribute(TAG_COLOR));
		IToken comment = new Token(new BasicTextAttribute(COMMENT_COLOR));
		IToken lemma = new Token(new BasicTextAttribute(LEMMA_COLOR));
		IToken string = new Token(new BasicTextAttribute(STRING_COLOR));
		IToken def = new Token(new BasicTextAttribute(DEFAULT_TAG_COLOR));
		
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
		
		setRules(rules);
	}
}
