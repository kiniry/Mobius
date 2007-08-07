/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions;

import umbra.UmbraHelper;


/**
 * This is a class for a special bytecode lines located after
 * the headers or at the end of the method,
 * containing some method data, not to be edited by a user.
 *
 * TODO lines of which kind of file are checked here?
 *
 * @author Tomek Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @version a-01
 */
public class CodeLineController extends BytecodeLineController {

  /**
   * The constant gives position in the line before which (<) the
   * text "max_stack=" must occur.
   */
  private static final int MAX_STACK_BOUND = 6;

  /**
   * The constant gives position in the line strictly before which (<) the
   * parenthesis character must occur.
   */
  private static final int PARENTHESIS_BOUND = 5;

  /**
   * This constructor remembers only the line text of the line with the "Code"
   * keyword.
   *
   * @param a_line_text the string representation of the line in the bytecode
   *               document
   * @see BytecodeLineController#BytecodeLineController(String)
   */
  public CodeLineController(final String a_line_text) {
    super(a_line_text);
  }

  /**
   * The line is correct if it contains one of four sets of
   * keywords. For lines starting with "Code" there is also
   * checked if all parameters are present reasonably set.
   * It is only for displaying information because modification of
   * these lines is not provided.
   *
   * @return <code>true</code> when the line contained in
   *         {@ref BytecodeLineController#my_line_text} contains a correct
   *         line from the bytecode file
   * @see BytecodeLineController#correct()
   */
  public final boolean correct() {
    //Code must exist because otherwise it would not be the class
    boolean res = false;
    final String my_line_text = getMy_line_text();
    if (my_line_text.startsWith("Code")) {
      res = correctCode();
    }
    if (my_line_text.startsWith("LineNumber")) {
      res = true;
    }
    if (my_line_text.startsWith("LocalVariable")) {
      res = correctLocalVariable();
    }
    if (my_line_text.startsWith("Attribute")) {
      res = correctAttribute();
    }

    return res;
  }

  /**
   * TODO.
   * @return TODO
   */
  private boolean correctAttribute() {
    final String s = UmbraHelper.stripAllWhitespace(getMy_line_text());
    if ((s.indexOf("(s)=")) > -1) {
      return true;
    }
    return false;
  }

  /**
   * TODO.
   * @return TODO
   */
  private boolean correctLocalVariable() {
    final String my_line_text = getMy_line_text();
    final String s = UmbraHelper.stripAllWhitespace(my_line_text);
    if ((s.indexOf("start_pc=")) > -1 &&
        (s.indexOf("length=")) > -1 &&
        (s.indexOf("index=")) > -1 &&
        (my_line_text.indexOf("start_pc")) > -1 &&
        (my_line_text.indexOf("length")) > -1 &&
        (my_line_text.indexOf("index")) > -1) {
      return true;
    }
    return false;
  }

  /**
   * TODO.
   * @return TODO
   */
  private boolean correctCode() {
    final String my_line_text = getMy_line_text();
    if (!(my_line_text.indexOf("(") > 0))
      return false;

    final String s = UmbraHelper.stripAllWhitespace(my_line_text);
    int i = 0;
    //czy jest to co trzeba
    if (!(s.indexOf("max_stack=") > 0))
      return false;
    if (!(s.indexOf(",max_locals=") > 0))
      return false;
    if (!(s.indexOf(",code_length=") > 0))
      return false;
    //czy liczby sa poprawne
    for (i = UmbraHelper.getIndexAfter(s, "max_stack=");
         i < (s.indexOf(",max_locals=")); i++) {
      if (!(Character.isDigit(s.charAt(i))))
        return false;
    }
    for (i = UmbraHelper.getIndexAfter(s, ",max_locals=");
         i < (s.indexOf(",code_length=")); i++) {
      if (!(Character.isDigit(s.charAt(i))))
        return false;
    }
    for (i = UmbraHelper.getIndexAfter(s, ",code_length=");
         i < (s.indexOf(")")); i++) {
      if (!(Character.isDigit(s.charAt(i))))
        return false;
    }
    //is the sequence of items right?
    // XXX: probably not necessary because we do the check below
    if ((s.indexOf("Code")) > (s.indexOf("(")))
      return false;
    if ((s.indexOf("(")) > (s.indexOf("max_stack=")))
      return false;
    if ((s.indexOf("max_stack=")) > (s.indexOf(",max_locals=")))
      return false;
    if ((s.indexOf(",max_locals=")) > (s.indexOf(",code_length=")))
      return false;
    if ((s.indexOf(",code_length")) > (s.indexOf(")")))
      return false;
    //are there numbers at all
    if (isOneStrictlyAfterAnother(s, "max_stack=", ",max_locals="))
      return false;
    if (isOneStrictlyAfterAnother(s, ",max_locals=", ",code_length="))
      return false;
    if (isOneStrictlyAfterAnother(s, ",code_length=", ")"))
      return false;
    //czy nawiasy poprawnie tzn jak po ) cos to zle
    if ((s.indexOf(")")) + 1 < (s.length()))
      return false;

    //is the sequence ok?
    if ((s.indexOf("Code")) < (s.indexOf("(")) &&
        (s.indexOf("(")) < (s.indexOf("max_stack=")) &&
        (s.indexOf("max_stack=")) < (s.indexOf(",max_locals=")) &&
        (s.indexOf(",max_locals=")) < (s.indexOf(",code_length=")) &&
        (s.indexOf(",code_length")) < (s.indexOf(")")) &&
        (s.indexOf("(")) < PARENTHESIS_BOUND &&
        (s.indexOf("max_stack=")) < MAX_STACK_BOUND) {
      return true;
    }
    return false;
  }

  /**
   * This method checks if the string <code>a_string2</code> starts in the
   * string <code>a_string0</code> farther than at the first position after
   * the string <code>a_string1</code>. This works properly only when
   * the strings <code>a_string1</code>, <code>a_string2</code> actually
   * occur in <code>a_string</code> and this condition is not checked here.
   *
   * @param a_string0 a string in which the positions are checked
   * @param a_string1 the string to occur first
   * @param a_string2 the string to occur next
   * @return <code>true</code> when <code>a_string2</code> occrus after
   * <code>a_string2</code>
   */
  private boolean isOneStrictlyAfterAnother(final String a_string0,
                                            final String a_string1,
                                            final String a_string2) {
    final int len = a_string1.length() + 1;
    return ((a_string0.indexOf(a_string1)) + len) >
            (a_string0.indexOf(a_string2));
  }
}
