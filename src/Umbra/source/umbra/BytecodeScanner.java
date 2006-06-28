package umbra;

import org.eclipse.jface.text.rules.EndOfLineRule;
import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.NumberRule;
import org.eclipse.jface.text.rules.RuleBasedScanner;
import org.eclipse.jface.text.rules.SingleLineRule;
import org.eclipse.jface.text.rules.WhitespaceRule;
import org.eclipse.jface.text.rules.WordRule;

/**
 * This class is responsible for coloring all text in Bytecode
 * editor window according to some special 9 rules.
 * Colors are chosen as a token array with a particular style (param 'mod').
 * 
 * @author Wojciech W¹s
 */

public class BytecodeScanner extends RuleBasedScanner {
	
	public BytecodeScanner(ColorManager manager, int mod) {

		IToken[] tokens = TokenGetter.getTokenTab(manager, mod); 
				
		WordRule insrule = new WordRule(new BytecodeWordDetector(), tokens[IColorValues.DEFAULT]);
		for (int i = 0; i < IBytecodeStrings.instructions.length; i++) {
			insrule.addWord(IBytecodeStrings.instructions[i], tokens[IColorValues.BTC_INSTR]);
		}
		
		
		for (int i = 0; i < IBytecodeStrings.linewords.length; i++) {
			insrule.addWord(IBytecodeStrings.linewords[i], tokens[IColorValues.LINE]);
		}
		
		for (int i = 0; i < IBytecodeStrings.code.length; i++) {
			insrule.addWord(IBytecodeStrings.code[i], tokens[IColorValues.LINE]);
		}
		
		WordRule keyrule = new WordRule(new SpecialWordDetector(), tokens[IColorValues.KEY]);
		
		IRule[] rules = new IRule[9];
		rules[0] = new EndOfLineRule("//", tokens[IColorValues.COMMENT]);
		rules[1] = insrule;
		rules[2] = new SpecialNumberRule('\n', ':', tokens[IColorValues.POSITION]);
		rules[3] = new SpecialNumberRule('#', tokens[IColorValues.HASH]);
		rules[4] = new SpecialNumberRule('%', tokens[IColorValues.ATTR]);
		rules[5] = new SpecialNumberRule('(', ')', tokens[IColorValues.SQUARE]);
		//rules[6] = keyrule;
		rules[6] = new SingleLineRule("{", "}", tokens[IColorValues.SQUARE]);
		rules[7] = new NumberRule(tokens[IColorValues.NUMBER]);
		rules[8] = new WhitespaceRule(new BytecodeWhitespaceDetector());

		setRules(rules);
	}
	
}

