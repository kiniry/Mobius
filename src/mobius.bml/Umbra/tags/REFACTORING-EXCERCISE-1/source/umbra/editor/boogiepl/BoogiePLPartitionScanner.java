/*
 * @title       "BoogiePL in Umbra"
 * @description "BoobiePL support for Umbra bytecode editor"
 * @copyright   ""
 * @license     ""
 */
package umbra.editor.boogiepl;

import org.eclipse.jface.text.rules.EndOfLineRule;
import org.eclipse.jface.text.rules.IPredicateRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.MultiLineRule;
import org.eclipse.jface.text.rules.RuleBasedPartitionScanner;
import org.eclipse.jface.text.rules.Token;

import umbra.editor.parsing.TagRule;

/**
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @author Wojciech Was (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */
public class BoogiePLPartitionScanner extends RuleBasedPartitionScanner {

  /**
   * TODO.
   */
  public static final String DEFAULT = "__xml_default";

  /**
   * TODO.
   */
  public static final String HEAD = "__xml_head";

  /**
   * TODO.
   */
  public static final String THROWS = "__xml_thr";

  /**
   * TODO.
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
  private static final int NUMBER_OF_RULES = 7;

  /**
   * TODO.
   */
  public BoogiePLPartitionScanner() {

    final IToken thr = new Token(THROWS);
    final IToken head = new Token(HEAD);
    final IToken tag = new Token(TAG);

    setPredicateRulesForMe(thr, head, tag);
  }

  /**
   * TODO.
   * @param a_throws_token TODO
   * @param a_head_token TODO
   * @param a_tag_token TODO
   */
  private void setPredicateRulesForMe(final IToken a_throws_token,
                                      final IToken a_head_token,
                                      final IToken a_tag_token) {
    final IPredicateRule[] rules = new IPredicateRule[NUMBER_OF_RULES];

    rules[COMMENT_RULE] = new MultiLineRule("<!--", "-->", a_head_token);
    rules[TAG_RULE] = new TagRule(a_tag_token);
    rules[PUBLIC_RULE] = new EndOfLineRule("public", a_head_token);
    rules[PRIVATE_RULE] = new EndOfLineRule("private", a_head_token);
    rules[PROTECTED_RULE] = new EndOfLineRule("protected", a_head_token);
    rules[BRACE_RULE] = new EndOfLineRule("}", a_head_token);
    rules[THROWS_RULE] = new EndOfLineRule("throws", a_throws_token);

    setPredicateRules(rules);
  }
}
