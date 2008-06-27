package ie.ucd.bon.plugin.editor;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jface.text.TextAttribute;
import org.eclipse.jface.text.rules.EndOfLineRule;
import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.RuleBasedScanner;
import org.eclipse.jface.text.rules.SingleLineRule;
import org.eclipse.jface.text.rules.Token;
import org.eclipse.jface.text.rules.WhitespaceRule;
import org.eclipse.jface.text.rules.WordRule;

public class BONCodeScanner extends RuleBasedScanner {

	private static final String[] KEYWORDS = { 
		"action", 
		"creator",
		"not",
		"reused",
		"and",
		"Current",
		"feature",
		"object",
		"root",
		"calls",
		"deferred",
		"for_all",
		"object_group",
		"scenario", 
		"class_chart", 
		"class", 
		"delta",
		"incoming", 
		"object_stack", 
		"scenario_chart", 
		"description", 
		"indexing", 
		"old", 
		"static_diagram", 
		"client", 
		"dictionary", 
		"infix", 
		"or", 
		"string_marks", 
		"cluster", 
		"dynamic_diagram", 
		"inherit", 
		"outgoing", 
		"such_that", 
		"cluster_chart", 
		"effective", 
		"interfaced", 
		"part", 
		"system_chart", 
		"command", 
		"end", 
		"invariant", 
		"persistent", 
		"component", 
		"ensure", 
		"involves", 
		"prefix", 
		"Void", 
		"concatenator", 
		"event", 
		"it_holds", 
		"query", 
		"xor", 
		"constraint", 
		"event_chart", 
		"keyword_prefix", 
		"redefined", 
		"creates", 
		"exists", 
		"member_of", 
		"require", 
		"creation_chart", 
		"explanation", 
		"nameless"
		
	};
	
	private static final String[] CONSTANTS = { 
		"false",
		"true", 
		"Result" 
	};	
	
	public BONCodeScanner(BONColourProvider provider) {
		
		IToken keyword = new Token(new TextAttribute(provider.getColour(BONColourProvider.KEYWORD)));
		IToken constant = new Token(new TextAttribute(provider.getColour(BONColourProvider.KEYWORD)));
		IToken comment = new Token(new TextAttribute(provider.getColour(BONColourProvider.SINGLE_LINE_COMMENT)));
		IToken string = new Token(new TextAttribute(provider.getColour(BONColourProvider.STRING)));
		IToken defaultToken = new Token(new TextAttribute(provider.getColour(BONColourProvider.DEFAULT)));
		
		//Rules data structure
		List<IRule> rules= new ArrayList<IRule>();
		
		// Add rule for single line comments.
		rules.add(new EndOfLineRule("//", comment));
		
		// Add rule for strings and character constants.
		rules.add(new SingleLineRule("\"", "\"", string, '\\'));
		rules.add(new SingleLineRule("'", "'", string, '\\'));
		
		// Add generic whitespace rule.
		rules.add(new WhitespaceRule(new BONWhitespaceDetector()));
		
		WordRule wordRule = new WordRule(new BONWordDector(), defaultToken);
		for (String word : KEYWORDS) {
			wordRule.addWord(word, keyword);
		}
		for (String word : CONSTANTS) {
			wordRule.addWord(word, constant);
		}
		rules.add(wordRule);
		
		
		IRule[] result= new IRule[rules.size()];
		rules.toArray(result);
		setRules(result);		
	}
	
	
}
