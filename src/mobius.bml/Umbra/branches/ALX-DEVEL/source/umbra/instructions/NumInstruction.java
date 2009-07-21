/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions;

/**
 * This is abstract class for all instructions with a number as a
 * parameter.
 *
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @version a-01
 */
public class NumInstruction extends MultiInstruction {


  /**
   * This creates an instance of an instruction
   * named as <code>a_name</code> in a line the text of which is
   * <code>a_line_text</code>. Currently it just calls the constructor of the
   * superclass.
   *
   * @param a_line_text the line number of the instruction
   * @param a_name the mnemonic name of the instruction
   * @see InstructionLineController#InstructionLineController(String, String)
   */
  public NumInstruction(final String a_line_text, final String a_name) {
    super(a_line_text, a_name);
  }

  /**
   * The method checks if the instruction <code>an_instr</code> occurs
   * correctly formatted in the line <code>a_line</code>. TODO more details
   *
   * @param a_line a bytecode line with all the whitespace stripped
   * @param an_instr an instruction text to be checked
   * @param a_char_label the character which delimits the number
   * @return -1 when we know that the syntax is wrong, 1 when we know the
   *         syntax is OK, 0 when we do not know, but we must search further
   */
  protected int checkInstructionWithNumber(final String a_line,
                                           final String an_instr,
                                           final char a_char_label) {
    final String my_line_text = getMy_line_text();
    //if some of the instructions starts not at the first position (?)
    //and not later than 2 chars after ':' then we check further
    if ((a_line.indexOf(an_instr) > 0) &&
        (a_line.indexOf(an_instr) <= a_line.indexOf(":") + 1))
      //if a_char_label is right after the instruction
      if (a_line.indexOf(an_instr) +
          (an_instr.length()) + 1 > a_line.indexOf(a_char_label)) {
        //then the rest must be digits
        for (int y = (a_line.indexOf(a_char_label) + 1);
             y < a_line.length(); y++) {
          if (!(Character.isDigit(a_line.charAt(y)))) return -1;
        }
        //checking if there are two numbers or one
        int a, b, d, e, f, g;
        //a is the length of the number as computed from the text with
        //whitespase stripped off
        a = (a_line.length() - a_line.indexOf(a_char_label));
        int c = 0;
        e = my_line_text.length() - my_line_text.indexOf(a_char_label);
        f = 0;
        g = my_line_text.length();
        for (d = 0; d < e; d++) {
          if (Character.isDigit(my_line_text.charAt(g - d - 1))) {
            f = 1;
          }
          if (f == 0 &&
              Character.isWhitespace(my_line_text.charAt(g - d - 1))) {
            c++;
          }
        }
        b = e - c;
        if (a == b)
          return 1;
      }
    return 0;
  }
}
