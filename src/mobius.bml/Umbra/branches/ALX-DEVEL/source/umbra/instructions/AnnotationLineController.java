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
 * This is a class that contains some information.
 * TODO
 *
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */
public class AnnotationLineController extends BytecodeLineController {

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
   * TODO.
   * @return TODO
   * @see BytecodeLineController#correct()
   */
  public final boolean correct()
  {
    return true;
  }
}
