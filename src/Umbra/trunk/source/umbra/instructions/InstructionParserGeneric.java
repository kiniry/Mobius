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
 * This class is the initial part of the byte code instruction parser class.
 * This parser is constructed as a sequence of subclasses that define various
 * parts of the parser functionality. This class contains the most basic
 * operations e.g. to swallow whitespace characters or to swallow delimiter
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class InstructionParserGeneric {

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
   * This constructor sets the string to be parsed and resets the parser
   * so that it is ready to analyse the content. The constructor can
   * only be called from subclasses.
   *
   * @param a_line the line with the content to parse
   */
  protected InstructionParserGeneric(final String a_line) {
    my_line = a_line;
    resetParser();
  }

  /**
   * This method swallows all the whitespace starting from the current
   * position of the index. This method may not advance the index in case
   * the first character to be analysed is not whitespace.
   *
   * @return <code>true</code> when the further analysis is not finished yet,
   *   <code>false</code> when at the end of the string
   */
  public boolean swallowWhitespace() {
    if (my_index == my_line.length() || my_line.substring(my_index).
                startsWith(InstructionParserHelper.getEOL()))
      return false;
    while (Character.isWhitespace(my_line.charAt(my_index))) {
      my_index++;
      if (my_index == my_line.length() ||
          my_line.substring(my_index).
                  startsWith(InstructionParserHelper.getEOL())) return false;
    }
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
   * Returns the content of the line which is parsed.
   *
   * @return the content of the current line
   */
  public String getLine() {
    return my_line;
  }

  /**
   * Returns the current index in the parsed line.
   *
   * @return the index in the current line
   */
  public int getIndex() {
    return my_index;
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

  /*@
    @ ensures my_index == \old(my_index) + 1;
    @*/
  /**
   * This method moves the index inside the parser one position forward.
   *
   * @return the new value of the index
   */
  public int incIndex() {
    return ++my_index;
  }

  /*@
    @ requires 0 <=  a_step && a_step <= my_line.length() - my_index ||
    @          - my_index <= a_step &&  a_step < 0;
    @ ensures my_index == \old(my_index) + a_step;
    @*/
  /**
   * This method moves the index inside the parser the given number of positions
   * forward.
   *
   * @param a_step a number by which the index is advanced
   * @return the new value of the index
   */
  public int moveIndex(final int a_step) {
    my_index += a_step;
    return my_index;
  }

  /**
   * @return <code>true</code> when the index is at the end of the parsed
   *   string
   */
  public boolean isFinished() {
    return my_index == my_line.length();
  }
}
