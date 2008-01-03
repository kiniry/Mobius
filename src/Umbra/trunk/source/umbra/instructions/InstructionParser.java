/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2007-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions;

/**
 * This class allows to parse the line with instruction. It enables the
 * analysis of the correctness.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class InstructionParser {

  /**
   * This field contains the value of the instruction line
   * which is parsed.
   */
  private String my_line;

  /**
   * The pointer inside the line. It points ot the first character which
   * has not been analysed yet. If this field is equal to my_line.length()
   * the analysis is finished.
   */
  private int my_index;
  //@ invariant 0 <= my_index && my_index <= my_line.length();

  /**
   * This field contains the number parsed from the chunk of the digits.
   * It contains a sensible value right after the {@ref #swallowNumber()}
   * is called.
   */
  private int my_result;

  /**
   * This constructor sets the string to be parsed and resets the parser
   * so that it is ready to analyse the content.
   *
   * @param a_line the line with the content to parse
   */
  public /*@ pure @*/ InstructionParser(final String a_line) {
    my_line = a_line;
    resetParser();
  }

  /*@
    @ ensures my_index == 0;
    @*/
  /**
   * This method resets the parser so that it starts the analysis
   * from the beginning.
   */
  public void resetParser() {
    my_index = 0;
  }

  /**
   * This method swallows all the whitespace starting from the current
   * position of the index. This method may not advance the index in case
   * the first character to be analysed is not whitespace.
   *
   * @return <code>true</code> when the further analysis is not finished yet,
   *   <code>false</code> otherwise
   */
  public boolean swallowWhitespace() {
    if (my_index == my_line.length()) return false;
    while (Character.isWhitespace(my_line.charAt(my_index))) {
      my_index++;
      if (my_index == my_line.length()) return false;
    }
    return true;
  }

  /**
   * This method swallows all the digits starting from the current
   * position of the index. This method may not advance the index in case
   * the first character to be analysed is not a digit or the analysis is
   * finished before the method is called. This method assumes that a
   * number is finished when a whitespace or end of string is met.
   * In case the whitespace is not met after the string the number is not
   * considered to be successfully swallowed.
   *
   * @return <code>true</code> when a number was successfully swallowed,
   *   <code>false</code> otherwise
   */
  public boolean swallowNumber() {
    boolean res = true;
    if (my_index == my_line.length()) res = false;
    final int oldindex = my_index;
    while (Character.isDigit(my_line.charAt(my_index)) && res) {
      my_index++;
      if (my_index == my_line.length()) break;
    }
    if (oldindex == my_index) return false; //no digits were read
    if (my_index < my_line.length() &&
        !Character.isWhitespace(my_line.charAt(my_index)))
      // the line is not finished and the character at index is not whitespace
      return false;
    my_result = Integer.parseInt(my_line.substring(oldindex, my_index));
    return true;
  }

  /**
   * This method swallows the given delimiter. This method may not advance
   * the index in case the first character to be analysed is not the delimiter
   * or the analysis is finished before the method is called.
   *
   * @param a_ch the character with the delimiter to swallow
   * @return <code>true</code> when the delimiter was successfully swallowed,
   *   <code>false</code> otherwise
   */
  public boolean swallowDelimiter(final char a_ch) {
    if (my_index == my_line.length()) return false;
    if (my_line.charAt(my_index) == a_ch) {
      my_index++;
      return true;
    }
    return false;
  }

  /**
   * Checks if the line at the current position starts with a mnemonic from
   * the inventory.
   *
   * @param the_inventory the array of the mnemonics to be checked
   * @return the index to the entry in the inventory which contains the
   *   mnemonic or -1 in case no mnemonic from the inventory occurs
   */
  public int swallowMnemonic(final String[] the_inventory) {
    int res = -1;
    for (int i = 0; i < the_inventory.length; i++) {
      if (my_line.indexOf(the_inventory[i], my_index) == my_index) {
        if (res == -1 ||
            the_inventory[res].length() >  the_inventory[i].length())
          res = i;
      }
    }
    return res;
  }

  /**
   * @return the number which is the result of parsing
   */
  public int getResult() {
    return my_result;
  }

  /**
   * @return <code>true</code> when the index is at the end of the parsed
   *   string
   */
  public boolean isFinished() {
    return my_index == my_line.length();
  }
}
