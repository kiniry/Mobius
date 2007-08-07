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
   * TODO.
   */
  public static final String DEFAULT = "__btc.default";

  /**
   * This is the name of a content type assigned to areas of a bytecode
   * document that correspond to headers of methods or classes. These
   * include {@link #COMMENT_RULE}, {@link #PUBLIC_RULE}, {@link #PRIVATE_RULE},
   * {@link #PROTECTED_RULE}, rules for braces, and {@link #CLASS_RULE}.
   */
  public static final String HEAD = "__btc.header";

  /**
   * TODO.
   */
  public static final String THROWS = "__btc.throwssec";

  /**
   * TODO.
   */
  public static final String TAG = "__btc.bmlcode";


  /**
   * TODO.
   */
  private static final int COMMENT_RULE = 0;

  /**
   * TODO.
   */
  private static final int BML_RULE = 1;

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
  private static final int OPEN_BRACE_RULE = 5;

  /**
   * TODO.
   */
  private static final int CLOSE_BRACE_RULE = 6;

  /**
   * TODO.
   */
  private static final int THROWS_RULE = 7;

  /**
   * TODO.
   */
  private static final int CLASS_RULE = 8;

  /**
   * The total number of rules in the current scanner.
   */
  private static final int NUMBER_OF_RULES = 9;

  /**
   * TODO.
   */
  public BytecodePartitionScanner() {

    final IToken thr = new Token(THROWS);
    final IToken head = new Token(HEAD);
    final IToken tag = new Token(TAG);

    final IPredicateRule[] rules = new IPredicateRule[NUMBER_OF_RULES];

    rules[COMMENT_RULE] = new MultiLineRule("<!--", "-->", head);
    rules[BML_RULE] = new MultiLineRule("/*", "*/", tag);
    rules[PUBLIC_RULE] = new EndOfLineRule("public", head);
    rules[PRIVATE_RULE] = new EndOfLineRule("private", head);
    rules[PROTECTED_RULE] = new EndOfLineRule("protected", head);
    rules[OPEN_BRACE_RULE] = new EndOfLineRule("{", head);
    rules[CLOSE_BRACE_RULE] = new EndOfLineRule("}", head);
    rules[THROWS_RULE] = new EndOfLineRule("throws", thr);
    rules[CLASS_RULE] = new EndOfLineRule("class", head);

    setPredicateRules(rules);
  }
}
