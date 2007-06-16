package umbra.editor.parsing;

import org.eclipse.jface.text.rules.*;

/**
 * @author Generated automatically
 */

public class BytecodePartitionScanner extends RuleBasedPartitionScanner {

  /**
   * TODO
   */
  public static final String DEFAULT = "__xml_default";
  /**
   * TODO
   */
  public static final String HEAD = "__xml_head";
  /**
   * TODO
   */
  public static final String THROWS = "__xml_thr";
  /**
   * TODO
   */
  public static final String TAG = "__xml_tag";

  /**
   * TODO
   *
   */
  public BytecodePartitionScanner() {

    final IToken thr = new Token(THROWS);
    final IToken head = new Token(HEAD);
    final IToken tag = new Token(TAG);

    final IPredicateRule[] rules = new IPredicateRule[8];

    rules[0] = new MultiLineRule("<!--", "-->", head);
    rules[1] = new TagRule(tag);
    rules[2] = new EndOfLineRule("class", head);
    rules[3] = new EndOfLineRule("public", head);
    rules[4] = new EndOfLineRule("private", head);
    rules[5] = new EndOfLineRule("protected", head);
    rules[6] = new EndOfLineRule("}", head);
    rules[7] = new EndOfLineRule("throws", thr);

    setPredicateRules(rules);
  }
}
