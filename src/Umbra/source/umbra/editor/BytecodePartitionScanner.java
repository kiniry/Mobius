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
   * TODO.
   */
  private static final int COMMENT_RULE = 0;

  /**
   * TODO.
   */
  private static final int TAG_RULE = 1;

  /**
   * TODO.
   */
  private static final int PUBLIC_RULE = 2;

  /**
   * TODO.
   */
  private static final int PRIVATE_RULE = 3;

  /**
   * TODO.
   */
  private static final int PROTECTED_RULE = 4;

  /**
   * TODO.
   */
  private static final int BRACE_RULE = 5;

  /**
   * TODO.
   */
  private static final int THROWS_RULE = 6;

  /**
   * TODO.
   */
  private static final int RULES_NUMBER = 7;


  /**
   * TODO
   */
  public BytecodePartitionScanner() {

    final IToken thr = new Token(THROWS);
    final IToken head = new Token(HEAD);
    final IToken tag = new Token(TAG);

    final IPredicateRule[] rules = new IPredicateRule[RULES_NUMBER];

    rules[COMMENT_RULE] = new MultiLineRule("<!--", "-->", head);
    rules[TAG_RULE] = new TagRule(tag);
    rules[PUBLIC_RULE] = new EndOfLineRule("public", head);
    rules[PRIVATE_RULE] = new EndOfLineRule("private", head);
    rules[PROTECTED_RULE] = new EndOfLineRule("protected", head);
    rules[BRACE_RULE] = new EndOfLineRule("}", head);
    rules[THROWS_RULE] = new EndOfLineRule("throws", thr);

    setPredicateRules(rules);
  }
}
