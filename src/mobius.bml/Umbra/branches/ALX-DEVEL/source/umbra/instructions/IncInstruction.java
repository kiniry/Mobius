/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions;

import org.apache.bcel.generic.IINC;
import org.apache.bcel.generic.Instruction;

import umbra.UmbraHelper;
import umbra.UmbraPlugin;
import umbra.editor.parsing.BytecodeStrings;


/**
 * This class is related to some subset of instructions
 * depending on parameters. It redefines some crucial while
 * handling with single instruction methods(correctness, getting handle).
 * This is only dealing with iinc instruction.
 *
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class IncInstruction extends NumInstruction {

  /**
   * TODO.
   */
  private static final int NUMBERS_NO = 2;

  /**
   * This creates an instance of an instruction
   * named as <code>a_name</code> in a line the text of which is
   * <code>a_line</code>. Currently it just calls the constructor of the
   * superclass.
   *
   * @param a_line_text the line number of the instruction
   * @param a_name the mnemonic name of the instruction
   * @see InstructionLineController#InstructionLineController(String, String)
   */
  public IncInstruction(final String a_line_text, final String a_name) {
    super(a_line_text, a_name);
  }


  /**
   * Inc instruction line is correct if it has
   * two simple number parameters (first preceded with %).
   *
   * @return TODO
   * @see InstructionLineController#correct()
   * @see InstructionLineController#chkcorr(String, String)
   */
  public final boolean correct() {
    return super.chkcorr(getMy_line_text(), "W%DW?-D?W");
  }

  /**
   * TODO.
   * @return TODO
   */
  public final boolean correct0() {
    final String my_line_text = getMy_line_text();
    final String s = UmbraHelper.stripAllWhitespace(my_line_text);
    final String[] s2 = BytecodeStrings.INCC_INS;
    int j;
    int y;
    UmbraPlugin.LOG.print(s);
    if (s.indexOf("%") < s.indexOf(":") + 1) {
      UmbraPlugin.LOG.print("hej1");
      return false;
    }
    boolean isminus = false;
    for (j = 0; j < s2.length; j++) {
      if ((s.indexOf(s2[j]) > 0) &&
          (s.indexOf(s2[j]) <= s.indexOf(":") + 1))
        if (s.indexOf(s2[j]) + (s2[j].length()) + 1 > s.indexOf("%")) {
          for (y = (s.indexOf("%") + 1); y < s.length(); y++) {
            if (!(Character.isDigit(s.charAt(y)))) {
              UmbraPlugin.LOG.print("tu ten minus " + s + " " + my_line_text);
              if (isminus)
                return false;
              else if (s.charAt(y) == '-')
                isminus = true;
              else
                return false;
            }
          }
          int counter = 0;
          boolean lastisdig = false;
          for (y = ((my_line_text.indexOf(s2[j])) + (s2[j].length()) + 1);
               y < my_line_text.length(); y++) {
            if (Character.isDigit(my_line_text.charAt(y))) {
              if (!(lastisdig)) counter++;
              lastisdig = true;
            } else
              if (Character.isWhitespace(my_line_text.charAt(y))) {
                lastisdig = false;
              }
          }
          if (counter == NUMBERS_NO) return true;
        }

    }
    return false;
  }

  /**
   * TODO.
   * @return TODO
   */
  private int getInd1() {
    final String my_line_text = getMy_line_text();
    boolean isd;
    final String licznik = "0123456789";
    int number = 0;

    isd = true;
    int dokad = my_line_text.length();
    for (int i = my_line_text.lastIndexOf("%") + 1;
         i < my_line_text.length(); i++) {
      if (!Character.isDigit(my_line_text.charAt(i))) {
        dokad = i;
        break;
      }
    }
    if (isd) {
      number = 0;
      for (int i = my_line_text.lastIndexOf("%") + 1; i < dokad; i++) {
        number = 10 * number +
                              licznik.indexOf(my_line_text.substring(i, i + 1));
      }
      return number;
    }
    return 0;
  }

  /**
   * TODO.
   * @return TODO
   */
  private int getInd2() {
    final String my_line_text = getMy_line_text();
    boolean isd;
    final String licznik = "0123456789";
    int number = 0;

    isd = true;
    //sets after first number parameter
    int skadskad = my_line_text.length();
    for (int i = my_line_text.lastIndexOf("%") + 1;
         i < my_line_text.length(); i++) {
      if (!Character.isDigit(my_line_text.charAt(i))) {
        skadskad = i;
        break;
      }
    }
    //sets the starting point of second number parameter
    int skad = 0;
    for (int i = skadskad; i < my_line_text.length(); i++) {
      if (Character.isDigit(my_line_text.charAt(i))) {
        skad = i;
        break;
      }
    }
    //sets the ending point of second number parameter
    int dokad = my_line_text.length();
    for (int i = skad; i < my_line_text.length(); i++) {
      if (!Character.isDigit(my_line_text.charAt(i))) {
        dokad = i;
        break;
      }
    }


    //always convert to int
    if (isd) {
      number = 0;
      for (int i = skad; i < dokad; i++) {
        number = 10 * number +
                 licznik.indexOf(my_line_text.substring(i, i + 1));
      }
      if (my_line_text.charAt(skad - 1) == '-') {
        number = number * (-1);
      }
      return number;
    }
    return 0;
  }

  /**
   * TODO.
   * @return TODO
   * @see BytecodeLineController#getInstruction()
   */
  public final Instruction getInstruction() {

    if (!correct())
      return null;

    int index1 = 0;
    index1 = getInd1();
    int index2 = 0;
    index2 = getInd2();

    if (getName().compareTo("iinc") == 0) {
      return new IINC(index1, index2);
    }

    return null;

  }
}
