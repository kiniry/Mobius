/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.editor.parsing;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.rules.EndOfLineRule;
import org.eclipse.jface.text.rules.IPredicateRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.MultiLineRule;
import org.eclipse.jface.text.rules.RuleBasedPartitionScanner;
import org.eclipse.jface.text.rules.Token;

import umbra.lib.BytecodeStrings;
import umbra.lib.EclipseIdentifiers;


/**
 * This class is responsible for dividing the byte code document into partitions
 * the colouring of which is governed by different rules. The text is
 * divided into four kinds of regions:
 * <ul>
 *   <li>default section (governed by {@link BytecodeScanner}),</li>
 *   <li>section for headers (e.g. method, class or package headers;
 *     governed by {@link NonRuleBasedDamagerRepairer}),</li>
 *   <li>section for throws sections (governed by
 *     {@link NonRuleBasedDamagerRepairer}),</li>
 *   <li>section for BML annotations (governed by
 *     {@link BytecodeBMLSecScanner}).</li>
 * </ul>
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @author Wojciech Was (ww209224@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class BytecodePartitionScanner extends RuleBasedPartitionScanner {

  /**
   * This is the name of a content type assigned to areas of a byte code
   * document that correspond to headers of methods or classes. These
   * include lines with comments, lines with public
   * declarations, lines with private declarations, lines with protected
   * declarations, lines with braces, and lines with class declarations.
   */
  public static final String SECTION_HEAD = "__btc.header";

  /**
   * This is the name of a content type assigned to areas of a byte code
   * document that correspond to constant pool.
   */
  public static final String SECTION_CP = "__btc.cp";

  /**
   * This is the name of a content type assigned to areas of a byte code
   * document that correspond to throws declarations.
   * FIXME: the handling of these sections is partial;
   *   https://mobius.ucd.ie/ticket/549
   */
  public static final String SECTION_THROWS = "__btc.throwssec";

  /**
   * This is the name of a content type assigned to areas of a byte code
   * document that correspond to BML annotations.
   */
  public static final String SECTION_BML = "__btc.bmlcode";

  /**
   * An array with the preconfigured content types of areas in a
   * bytecode file.
   */
  private static final String[] CONFIGURED_CONTENT_TYPES = new String[] {
    IDocument.DEFAULT_CONTENT_TYPE,
    BytecodePartitionScanner.SECTION_HEAD,
    BytecodePartitionScanner.SECTION_CP,
    BytecodePartitionScanner.SECTION_BML };

  /**
   * Index for the rule to handle BML annotations ending "@*\/".
   */
  private static final int BML_RULE = 0;

  /**
   * Index for the rule to handle BML annotations  ending "*\/".
   */
  private static final int BML_RULE_SIMPLE = 1;

  /**
   * Index for the rule to handle constant pool areas.
   */
  private static final int CP_RULE = 2;

  /**
   * Index for the rule to handle constant pool areas.
   */
  private static final int SCP_RULE = 3;

  /**
   * Index for the rule to handle throws lines.
   */
  private static final int THROWS_RULE = 4;

  /**
   * The total number of rules in the current scanner. It is by one greater
   * than the maximal rule number.
   */
  private static final int NUMBER_OF_RULES = THROWS_RULE + 1;

  /**
   * The string which indicates an empty line.
   */
  private static final String EMPTY_LINE_MARKER = 
    EclipseIdentifiers.EDITOR_EOL + EclipseIdentifiers.EDITOR_EOL;

  /**
   * This constructor creates rules and configures the scanner with them.
   * The rules handle the division of the byte code document into
   * partitions the colouring of which is governed by different rules. The text
   * is divided into four kinds of regions:
   * <ul>
   *   <li>default section,</li>
   *   <li>section for headers (e.g. method, class or package headers),</li>
   *   <li>section for throws sections,</li>
   *   <li>section for BML annotations.</li>
   * </ul>
   */
  public BytecodePartitionScanner() {
    final IToken head = new Token(SECTION_HEAD);
    final IPredicateRule[] rules = new IPredicateRule[NUMBER_OF_RULES +
      BytecodeStrings.HEADER_PREFIX.length + 1];
    generateFixedRules(rules);
    for (int i = 0; i < BytecodeStrings.HEADER_PREFIX.length; i++) {
      rules[NUMBER_OF_RULES + i] =
        new EndOfLineRule(BytecodeStrings.HEADER_PREFIX[i], head);
    }
    rules[NUMBER_OF_RULES + BytecodeStrings.HEADER_PREFIX.length] =
      new MethodRule(head);
    setPredicateRules(rules);
  }

  /**
   * This method generates the rules which occupy fixed number of entries
   * in the rules table.
   *
   * @param the_rules the rules table to fill in the actual rules
   */
  private void generateFixedRules(final IPredicateRule[] the_rules) {
    final IToken cp = new Token(SECTION_CP);
    final IToken thr = new Token(SECTION_THROWS);
    final IToken bml = new Token(SECTION_BML);
    the_rules[BML_RULE] = new MultiLineRule(BytecodeStrings.ANNOT_START,
                                        BytecodeStrings.ANNOT_END, bml);
    the_rules[BML_RULE_SIMPLE] = new MultiLineRule(
                                        BytecodeStrings.ANNOT_START,
                                        BytecodeStrings.ANNOT_END_SIMPLE,
                                        bml);
    the_rules[CP_RULE] = new MultiLineRule(BytecodeStrings.JAVA_KEYWORDS[
                                        BytecodeStrings.CP_KEYWORD_POS],
                                        EMPTY_LINE_MARKER,
                                        cp);
    the_rules[SCP_RULE] = new MultiLineRule(BytecodeStrings.JAVA_KEYWORDS[
                                        BytecodeStrings.SCP_KEYWORD_POS],
                                        EMPTY_LINE_MARKER,
                                        cp);
    the_rules[THROWS_RULE] = new EndOfLineRule(BytecodeStrings.THROWS_PREFIX[0],
                                               thr);
  }

  /**
   * Returns the preconfigured content types.
   *
   * @return the preconfigured content types
   */
  public static String[] getPreconfiguredContentTypes() {
    return CONFIGURED_CONTENT_TYPES;
  }
}
