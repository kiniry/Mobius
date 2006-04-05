package fr.inria.everest.coq.editor;

import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.MultiLineRule;
import org.eclipse.jface.text.rules.SingleLineRule;
import org.eclipse.jface.text.rules.WordRule;

import prover.gui.editor.BasicRuleScanner;
import prover.gui.editor.detector.ExprDetector;
import prover.gui.editor.detector.WordDetector;

public class CoqRuleScanner extends BasicRuleScanner implements ICoqColorConstants {
	
	public CoqRuleScanner() {
		super(CoqProverTranslator.getInstance().getFileRules());
	}
}
