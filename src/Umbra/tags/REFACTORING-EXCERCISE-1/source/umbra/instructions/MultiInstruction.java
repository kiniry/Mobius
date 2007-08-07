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
 * This is abstract class for all instructions with at least one
 * parameter.
 *
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @version a-01
 */
public class MultiInstruction extends InstructionLineController {

  /**
   * This creates an instance of an instruction
   * named as <code>a_name</code> at the line number
   * <code>a_line_text</code>. Currently it just calls the constructor of the
   * superclass.
   *
   * @param a_line_text the line number of the instruction
   * @param a_name the mnemonic name of the instruction
   * @see InstructionLineController#InstructionLineController(String, String)
   */
  public MultiInstruction(final String a_line_text, final String a_name) {
    super(a_line_text, a_name);
  }

}
