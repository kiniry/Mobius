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
 * This is abstract class for all instructions with a string (in or
 * without <>, always without "") as a parameter.
 *
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @version a-01
 */
public class StringInstruction extends MultiInstruction {

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
  public StringInstruction(final String a_line_text, final String a_name) {
    super(a_line_text, a_name);
  }

  /**
   * TODO.
   * @return TODO
   */
  protected int getInd() {
    final String my_line_text = getMy_line_text();
    boolean isd;
    final String licznik = "0123456789";
    int number;
    if (my_line_text.lastIndexOf("(") < my_line_text.lastIndexOf(")")) {
      isd = true;
      for (int i = my_line_text.lastIndexOf("(") + 1;
           i < my_line_text.lastIndexOf(")"); i++) {
        if (!Character.isDigit(my_line_text.charAt(i))) {
          isd = false;
        }
      }
      if (isd) {
        number = 0;
        for (int i = my_line_text.lastIndexOf("(") + 1;
             i < my_line_text.lastIndexOf(")"); i++) {
          number = 10 * number +
                              licznik.indexOf(my_line_text.substring(i, i + 1));
        }
        return number;
      }
    }
    return 0;
  }
}
