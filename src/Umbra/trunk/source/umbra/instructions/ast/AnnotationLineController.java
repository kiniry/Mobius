/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions.ast;

import umbra.lib.BytecodeStrings;



/**
 * This class handles the creation and correctness of line controllers that
 * contain BML annotations. The method number associated with the
 * <code>AnnotationLineController</code> that contains the specs of a
 * method is this method number.
 *
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class AnnotationLineController extends CommentLineController {

  /**
   * This constructor remembers only the line text with the BML annotations.
   *
   * @param a_line_text the string representation of the line for the line
   *               with the BML annotations
   * @see BytecodeLineController#BytecodeLineController(String)
   */
  public AnnotationLineController(final String a_line_text) {
    super(a_line_text);
  }

  /**
   * Checks the correctness of such lines. The Umbra parser considers them as
   * always correct. The actual check is done elsewhere (in BmlLib).
   *
   * @return <code>ture</code>
   * @see BytecodeLineController#correct()
   */
  public final boolean correct()
  {
    return true;
  }

  /**
   * The method checks if the given string can be the start of a BML annotation.
   * We use the heuristic that the line must start with "/*@" possibly
   * with some initial whitespace before the sequence.
   *
   * @param a_line the string to be checked
   * @return <code>true</code> when the string can start annotation.
   */
  public static boolean isAnnotationStart(
                              final /*@ non_null @*/ String a_line) {
    return a_line.trim().startsWith("/*@");
  }

  /**
   * Checks is the line can be an end of annotation. This holds when the
   * final non-whitespace sequence in the line is either
   * {@link BytecodeStrings#ANNOT_END} or
   * {@link BytecodeStrings#ANNOT_END_SIMPLE}.
   *
   * @return <code>true</code> when the line contains the end of comment
   *   sequence, <code>false</code> otherwise
   */
  public boolean isAnnotationEnd() {
    final String line = getMy_line_text();
    int where = line.lastIndexOf(BytecodeStrings.ANNOT_END);
    int wlen = BytecodeStrings.ANNOT_END.length();
    if (where == 0) {
      where = line.lastIndexOf(BytecodeStrings.ANNOT_END_SIMPLE);
      wlen = BytecodeStrings.ANNOT_END_SIMPLE.length();
    }
    if (where > 0) {
      where += wlen;
      for (int i = where; i < line.length(); i++) {
        if (!Character.isWhitespace(line.charAt(i))) return false;
      }
      return true;
    }
    return false;
  }
}
