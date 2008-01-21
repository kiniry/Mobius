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
   * This is the name of a content type assigned to areas of a byte code
   * document that correspond to headers of methods or classes. These
   * include lines with comments, lines with public
   * declarations, lines with private declarations, lines with protected
   * declarations, lines with braces, and lines with class declarations.
   */
  public static final String HEAD = "__btc.header";

  /**
   * TODO. lines with throws clauses,
   */
  public static final String THROWS = "__btc.throwssec";

  /**
   * TODO. lines with BML annotations,
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
   * Index for the rule to handle lines with public declarations.
   */
  private static final int PUBLIC_RULE = 2;

  /**
   * Index for the rule to handle lines with private declarations.
   */
  private static final int PRIVATE_RULE = 3;

  /**
   * Index for the rule to handle lines with protected declarations.
   */
  private static final int PROTECTED_RULE = 4;

  /**
   * Index for the rule to handle lines with the opening brace ({).
   */
  private static final int OPEN_BRACE_RULE = 5;

  /**
   * Index for the rule to handle lines with the closing brace (}).
   */
  private static final int CLOSE_BRACE_RULE = 6;

  /**
   * Index for the rule to handle lines with throws.
   */
  private static final int THROWS_RULE = 7;

  /**
   * Index for the rule to handle lines with class declarations.
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
    rules[BML_RULE] = new MultiLineRule("/*@", "@*/", tag);
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
