package umbra.editor.boogiepl;

import org.eclipse.jface.text.rules.*;

import umbra.editor.parsing.TagRule;

/**
 * @author Generated automatically
 */

public class BoogiePLPartitionScanner extends RuleBasedPartitionScanner {
  public static final String DEFAULT = "__xml_default";
  public static final String HEAD = "__xml_head";
  public static final String THROWS = "__xml_thr";
  public static final String TAG = "__xml_tag";

  public BoogiePLPartitionScanner() {

    final IToken thr = new Token(THROWS);
    final IToken head = new Token(HEAD);
    final IToken tag = new Token(TAG);

    final IPredicateRule[] rules = new IPredicateRule[7];

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
