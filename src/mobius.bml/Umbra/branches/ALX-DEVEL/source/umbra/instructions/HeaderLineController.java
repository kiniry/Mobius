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
 * This is a class for a special Bytecode lines at the beginning
 * of the method, not to be edited by a user.
 *
 * @author Tomek Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class HeaderLineController extends BytecodeLineController {

  /**
   * This constructor remembers only the line text of the line which contains
   * the header information. TODO which header?
   *
   * @param a_line_text the string representation of the line text
   * @see BytecodeLineController#BytecodeLineController(String)
   */
  public HeaderLineController(final String a_line_text) {
    super(a_line_text);
  }

  /**
   * TODO.
   * @return TODO
   */
  public final boolean correct()
  {
    //nie za bardzo mozna ustalic zaleznosci
    //zbior wyrazow przed innym niektore opcjonalne
    return true;
  }

  /**
   * The method index of the header is equal to
   * the previous line's one increased by one.
   * TODO
   *
   * @param an_index TODO
   */
  public final void setIndex(final int an_index) {
    super.setIndex(an_index + 1);
  }
}
