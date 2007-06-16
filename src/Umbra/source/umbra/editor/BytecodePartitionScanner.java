package umbra.editor;

import org.eclipse.jface.text.rules.*;

import umbra.editor.parsing.TagRule;

/**
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @author Wojciech Was (ww209224@students.mimuw.edu.pl)
 * @versin a-01
 */
public class BytecodePartitionScanner extends RuleBasedPartitionScanner {
  
  public static final String DEFAULT = "__xml_default";
  public static final String HEAD = "__xml_head";
  public static final String THROWS = "__xml_thr";
  public static final String TAG = "__xml_tag";

  public BytecodePartitionScanner() {

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
