package umbra;

import org.eclipse.jface.text.rules.*;

/**
 * @author Generated automatically
 */

public class BytecodePartitionScanner extends RuleBasedPartitionScanner {
	public final static String DEFAULT = "__xml_default";
	public final static String HEAD = "__xml_head";
	public final static String THROWS = "__xml_thr";
	public final static String TAG = "__xml_tag";

	public BytecodePartitionScanner() {

		IToken thr = new Token(THROWS);
		IToken head = new Token(HEAD);
		IToken tag = new Token(TAG);

		IPredicateRule[] rules = new IPredicateRule[7];

		rules[0] = new MultiLineRule("<!--", "-->", head);
		rules[1] = new TagRule(tag);
		rules[2] = new EndOfLineRule("public", head);
		rules[3] = new EndOfLineRule("private", head);
		rules[4] = new EndOfLineRule("protected", head);
		rules[5] = new EndOfLineRule("}", head);
		rules[6] = new EndOfLineRule("throws", thr);

		setPredicateRules(rules);
	}
}
