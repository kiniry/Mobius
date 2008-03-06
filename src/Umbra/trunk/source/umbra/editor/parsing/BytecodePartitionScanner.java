/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.editor.parsing;

import org.eclipse.jface.text.rules.EndOfLineRule;
import org.eclipse.jface.text.rules.IPredicateRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.MultiLineRule;
import org.eclipse.jface.text.rules.RuleBasedPartitionScanner;
import org.eclipse.jface.text.rules.Token;


/**
 * TODO.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @author Wojciech Was (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */
public class BytecodePartitionScanner extends RuleBasedPartitionScanner {

  /**
   * This is the name of a content type assigned to areas of a byte code
   * document that are not treated in a special way.
   */
  public static final String DEFAULT = "__btc.default";

  /**
   * This is the name of a content type assigned to areas of a byte code
   * document that correspond to headers of methods or classes. These
   * include lines with comments, lines with public
   * declarations, lines with private declarations, lines with protected
   * declarations, lines with braces, and lines with class declarations.
   */
  public static final String HEAD = "__btc.header";

  /**
   * This is the name of a content type assigned to areas of a byte code
   * document that correspond to throws declarations.
   */
  public static final String THROWS = "__btc.throwssec";

  /**
   * This is the name of a content type assigned to areas of a byte code
   * document that correspond to BML annotations.
   */
  public static final String TAG = "__btc.bmlcode";

  /**
   * Index for the rule to handle the XML comments.
   */
  private static final int COMMENT_RULE = 0;

  /**
   * Index for the rule to handle BML annotations.
   */
  private static final int BML_RULE = 1;

  /**
   * Index for the rule to handle throws lines.
   */
  private static final int THROWS_RULE = 2;

  /**
   * The total number of rules in the current scanner. It is by one greater
   * than the maximal rule number.
   */
  private static final int NUMBER_OF_RULES = 3;


  /**
   * TODO.
   */
  public BytecodePartitionScanner() {

    final IToken thr = new Token(THROWS);
    final IToken head = new Token(HEAD);
    final IToken tag = new Token(TAG);

    final IPredicateRule[] rules = new IPredicateRule[NUMBER_OF_RULES +
                              BytecodeStrings.HEADER_PREFIX.length];

    rules[COMMENT_RULE] = new MultiLineRule("<!--", "-->", head);
    rules[BML_RULE] = new MultiLineRule("/*@", "@*/", tag);
    rules[THROWS_RULE] = new EndOfLineRule("throws", thr);

    for (int i = 0; i < BytecodeStrings.HEADER_PREFIX.length;
         i++) {
      rules[NUMBER_OF_RULES + i] = new EndOfLineRule(
        BytecodeStrings.HEADER_PREFIX[i], head);
    }
    setPredicateRules(rules);
  }
}
