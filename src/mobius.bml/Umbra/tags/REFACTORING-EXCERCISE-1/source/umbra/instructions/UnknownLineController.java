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
 * This class is resposible for all lines that we cannot classify.
 *
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @version a-01
 */
public class UnknownLineController extends BytecodeLineController {

  /**
   * This constructor only remembers the line with the
   * unrecognized content.
   *
   * @param a_line_text the string representation of the line with unrecognized
   * content
   * @see BytecodeLineController#BytecodeLineController(String)
   */
  public UnknownLineController(final String a_line_text) {
    super(a_line_text);
  }

}
