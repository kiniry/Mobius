package prover.gui.editor;

import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.RuleBasedScanner;


public class BasicRuleScanner extends RuleBasedScanner implements IColorConstants {


	public BasicRuleScanner() {
		this(null);
	}
	
	public BasicRuleScanner(IRule[] rules) {
		super();
		if(rules == null) {
			rules = new IRule[0];
		}
		setRules(rules);
	}
	
	

	public IToken getDefaultReturnToken() {
		return fDefaultReturnToken;
	}
}
