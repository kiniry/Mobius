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
   * The constant to indicate one that the instruction has one parameter.
   */
  private static final int PARAMS_ONE = 1;

  /**
   * The constant to indicate one that the instruction has two parameters.
   */
  private static final int PARAMS_TWO = 2;

  /**
   * The first state when whitespace is scanned.
   */
  private static final int STATE_FIRST_WHITESPACE = 0;

  /**
   * The first state when a number is scanned.
   */
  private static final int STATE_FIRST_NUMBER = 1;

  /**
   * The state when whitespace is scanned between the first and the second
   * number.
   */
  private static final int STATE_SECOND_WHITESPACE = 2;

  /**
   * The second state when a number is scanned.
   */
  private static final int STATE_SECOND_NUMBER = 3;

  /**
   * The state when the final whitespace is scanned.
   */
  private static final int STATE_FINAL_WHITESPACE = 4;

  /**
   * The variable which contains the internal state for parsing.
   */
  private int my_parsestate;

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
   * correctly formatted in the line <code>a_line</code>.
   *
   * The line is incorrect when:
   * <ul>
   *   <li>it does not contain ":",</li>
   *   <li>the parameters of the opcodes are not decimal numbers.</li>
   * </ul>
   *
   * The line should be checked elsewhere when:
   * <ul>
   *   <li>the line does not contain the opcoce <code>an_instr</code>,</li>
   *   <li>the opcode is not followed by a delimiter from
   *       <code>a_char_label</code>,</li>
   *   <li>the line does not contain two parameters.</li>
   * </ul>
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
    int res = 0;
    // : must occur for the string to be correct
    if (a_line.indexOf(":") < 0) res = -1;
    //if the instruction starts right after the line number then
    //we proceed, otherwise we check another instruction
    if (res == 0 && a_line.indexOf(an_instr) == a_line.indexOf(":") + 1) {
      //if a_char_label is right after the instruction then we proceed,
      // otherwise we check another instruction
      if (a_line.indexOf(an_instr) +
          (an_instr.length()) + 1 > a_line.indexOf(a_char_label)) {
        //then the rest must be digits
        for (int y = (a_line.indexOf(a_char_label) + 1);
             y < a_line.length(); y++) {
          if (!(Character.isDigit(a_line.charAt(y)))) {
            res = -1;
            break;
          }
        }
        //checking if there are two numbers or one
        if (res == 0) {
          res = checkNoParameters(a_char_label);
          return res != 1 ? -1 : 1;
        }
      }
    }
    return res;
  }

  /**
   * This method checks the number of parameters in the instruction included
   * in <code>a_line</code>
   *
   * The parameters start right after <code>a_char_label</code> character
   * and are separated with whitespace. Any number of whitespace before
   * and after each parameter is allowed.
   *
   * @param a_char_label the delimiter of parameters
   * @return 1, 2 mean one and two parameters resp., in other cases -1 is
   *   returned
   */
  private int checkNoParameters(final char a_char_label) {
    final String my_line_text = getMy_line_text();
    my_parsestate = 0;
    for (int i = my_line_text.indexOf(a_char_label);
         i < my_line_text.length(); i++) {
      switch (my_parsestate) {
        case STATE_FIRST_WHITESPACE: //the first whitespace
          i = handleWhitespace(my_line_text, i);
          break;
        case STATE_FIRST_NUMBER: //the first number
          i = handleNumber(my_line_text, i);
          break;
        case STATE_SECOND_WHITESPACE: //the separator whitespace
          i = handleWhitespace(my_line_text, i);
          break;
        case STATE_SECOND_NUMBER: //the second number
          i = handleNumber(my_line_text, i);
          break;
        case STATE_FINAL_WHITESPACE: //the final whitespace
          i = handleWhitespace(my_line_text, i);
          break;
        default:
          break;
      }
    }
    return stateToParNumber();
  }

  /**
   * This method converts the current state number to the number of parameters.
   *
   * @return 2 when my_parsestate is {@ref #STATE_SECOND_NUMBER} or
   *   {@ref #STATE_FINAL_WHITESPACE};
   *         1 when my_parsestate is {@ref #STATE_FIRST_NUMBER} or
   *   {@ref #STATE_SECOND_WHITESPACE};
   *        -1 otherwise
   */
  private int stateToParNumber() {
    if (my_parsestate == STATE_SECOND_NUMBER ||
        my_parsestate == STATE_FINAL_WHITESPACE)
      return PARAMS_TWO;
    if (my_parsestate == STATE_FIRST_NUMBER ||
        my_parsestate == STATE_SECOND_WHITESPACE)
      return PARAMS_ONE;
    return -1;
  }

  /**
   * Handle the state when a number is scanned. In case the character at
   * <code>an_i</code> in <code>a_line</code> is a digit do nothing. Otherwise,
   * advance the {@ref #my_parsestate} and decrease the counter
   * <code>an_i</code> to make sure the next state is checked for the same
   * position.
   *
   * @param a_line the text of the line
   * @param an_i the position in the line
   * @return <code>an_i - 1</code> when my_parsestate is advanced,
   *   <code>an_i</code> otherwise
   */
  private int handleNumber(final String a_line, final int an_i) {
    if (!Character.isDigit(a_line.charAt(an_i))) {
      my_parsestate++;
      return an_i - 1;
    }
    return an_i;
  }

  /**
   * Handle the state when whitespace is scanned. In case the character at
   * <code>an_i</code> in <code>a_line</code> is whitespace do nothing.
   * Otherwise, advance the {@ref #my_parsestate} and decrease the counter
   * <code>an_i</code> to make sure the next my_parsestate is checked for the
   * same position.
   *
   * @param a_line the text of the line
   * @param an_i the position in the line
   * @return <code>an_i - 1</code> when my_parsestate is advanced,
   *   <code>an_i</code> otherwise
   */
  private int handleWhitespace(final String a_line, final int an_i) {
    if (!Character.isWhitespace(a_line.charAt(an_i))) {
      my_parsestate++;
      return an_i - 1;
    }
    return an_i;
  }
}
