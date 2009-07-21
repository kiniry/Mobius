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
 * This is a class resposible for all lines which are regarded
 * to be an instruction but unable to classify.
 *
 * @author Tomek Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @version a-01
 */
public class UnclassifiedInstruction extends InstructionLineController {


  /**
   * This constructor creates an instruction which is not recognized. It stores
   * only the content of the line and the form of the mnemonic by calling
   * the superclass constructor.
   *
   * @param a_line_text the line with the unclassified mnemonic
   * @param a_name the unclassified mnemonic
   * @see InstructionLineController#InstructionLineController(String, String)
   */
  public UnclassifiedInstruction(final String a_line_text,
                                 final String a_name) {
    super(a_line_text, a_name);
  }
  /**
   * Instruction out of classification is never correct.
   *
   * @return <code>false</code>
   * @see  InstructionLineController#correct()
   */
  public final boolean correct() {
    return false;
  }
}
