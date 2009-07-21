/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions.ast;

import umbra.lib.BytecodeStrings;

/**
 * This class handles the creation and correctness of line controllers that
 * form comments.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class CommentLineController extends BytecodeLineController {

  /**
   * This constructor remembers only the line text with the comment content.
   *
   * @param a_line the string representation of the line for the line
   *               with comments
   * @see BytecodeLineController#BytecodeLineController(String)
   */
  public CommentLineController(final String a_line) {
    super(a_line);
  }

  /**
   * The method checks if the given string can be the start of a multi-line
   * comment.
   * We use the heuristic that the line must start with "/*" possibly
   * with some initial whitespace before the sequence.
   *
   * @param a_line the string to be checked
   * @return <code>true</code> when the string can start comment
   */
  public static boolean isCommentStart(
                              final /*@ non_null @*/ String a_line) {
    return a_line.trim().startsWith(BytecodeStrings.COMMENT_LINE_START);
  }


  /**
   * Checks is the line can be an end of comment. This holds when the
   * final non-whitespace sequence in the line is * / string.
   *
   * @return <code>true</code> when the line contains the end of comment
   *   sequence, <code>false</code> otherwise
   */
  public boolean isCommentEnd() {
    final String line = getMy_line_text();
    int where = line.lastIndexOf(BytecodeStrings.COMMENT_LINE_END);
    if (where > 0) {
      where += BytecodeStrings.COMMENT_LINE_END.length();
      for (int i = where; i < line.length(); i++) {
        if (!Character.isWhitespace(line.charAt(i))) return false;
      }
      return true;
    }
    return false;
  }

  /**
   * This method is used to check some basic condition of
   * correctness. For comment lines this is always true.
   *
   * @return  true if the instruction is correct
   * @see    InstructionLineController#correct()
   */
  public boolean correct()  {
    return true;
  }
}
