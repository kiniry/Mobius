/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions;

import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.LDC;
import org.apache.bcel.generic.LDC2_W;
import org.apache.bcel.generic.LDC_W;

import umbra.UmbraHelper;
import umbra.UmbraPlugin;
import umbra.editor.parsing.BytecodeStrings;


/**
 * This class is related to some subset of instructions
 * depending on parameters. It redefines some crucial while
 * handling with single instruction methods(correctness, getting handle).
 * These instruction are dealing with long data.
 *
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @version a-01
 */
public class LdcInstruction extends OtherInstruction {

  /**
   * A position before which the '(' character cannot occur in a correct line.
   */
  private static final int LEFT_PAREN_FORBIDDEN_BOUND = 2;

  /**
   * A position before which the ')' character cannot occur in a correct line.
   */
  private static final int RIGHT_PAREN_FORBIDDEN_BOUND = 2;

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
  public LdcInstruction(final String a_line_text, final String a_name) {
    super(a_line_text, a_name);
  }

  /**
   * TODO.
   * @return TODO
   */
  private int getInd() {
    final String my_line_text = getMy_line_text();
    boolean isd;
    final String licznik = "0123456789";
    int number;
    if (my_line_text.lastIndexOf("(") >= my_line_text.lastIndexOf(")")) {
      UmbraPlugin.messagelog("linia jest niepoprawna nic nie tworzy " +
                             my_line_text.lastIndexOf("(") + " " +
                             my_line_text.lastIndexOf(")"));
    } else {
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

  /**
   * TODO.
   * @return TODO
   * @see BytecodeLineController#getInstruction()
   */
  public final Instruction getInstruction() {
    int index;

    if (!correct())
      return null;
    Instruction res = null;
    index = getInd();
    if (getName().compareTo("ldc") == 0) {
      res = new LDC(index);
    }
    if (getName().compareTo("ldc_w") == 0) {
      res = new LDC_W(index);
    }
    if (getName().compareTo("ldc2_w") == 0) {
      res = new LDC2_W(index);
    }
    return res;
  }

  /**
   * Ldc instruction line is correct if it has
   * one main parameter that may be a simple number
   * as well as a string in "" and another one that
   * is a number in ().
   *
   * @return TODO
   * @see InstructionLineController#correct()
   */
  public final boolean correct()
  {
    String str;
    final String my_line_text = getMy_line_text();
    final String s = UmbraHelper.stripAllWhitespace(my_line_text);
    final String[] s2 = BytecodeStrings.LDC_INS;
    int j, y, okok, okokok;
    for (j = 0; j < s2.length; j++) {
      if ((s.indexOf(s2[j]) > 0) &&
          (s.indexOf(s2[j]) <= s.indexOf(":") + 1))
        if (s.indexOf(s2[j]) + (s2[j].length()) + 1 > s.indexOf("%"))
        {
        //parameter checking
          if (s.lastIndexOf("(") < LEFT_PAREN_FORBIDDEN_BOUND) return false;
          if (s.lastIndexOf(")") < RIGHT_PAREN_FORBIDDEN_BOUND) return false;
          int m, n, o;
          m = my_line_text.lastIndexOf("(");
          n = my_line_text.lastIndexOf(")");
          if (m + 1 >= n) {
            return false;
          }
          for (o = m + 1; o < n; o++) {
            if (!(Character.isDigit(my_line_text.charAt(o)))) return false;
          }
          //two types: number and (number) or string and (number)
          okok = 0;
          for (y = (s.indexOf(s2[j]) + s2[j].length());
               y < s.lastIndexOf("("); y++) {
            if (!(Character.isDigit(s.charAt(y)))) okok++;
          }
          okokok = 0;
          str = "\"\"";
          if (okok > 0) {
            if (((s.indexOf(s2[j]) + s2[j].length())) == s.indexOf("\"")) {
              //here is null, true or false, true charsetName
              //checking if there is second" and if there are are 2
              if (!(s.indexOf("\"") == (s.lastIndexOf("(") - 1))) {
                if ((s.charAt(s.lastIndexOf("(") - 1)) == str.charAt(1)) {
                  okokok++;
                }
              }
            }
          }

//        //if there are two numbers or one
          int c, d, e;
          int f, g, l;
          f = 0;
          g = 0;
          l = 0;
          e = my_line_text.lastIndexOf("(");
          d = my_line_text.indexOf(s2[j]) + s2[j].length();
          for (c = d; c < e; c++) {
            l = 0;
            if (Character.isDigit(my_line_text.charAt(c))) {
              f = 1;
            }
            if (f == 1) {
              if (!(Character.isDigit(my_line_text.charAt(c)))) {
                if (g == 1) {
                  l = 0;
                } else {
                  g = 1;
                  l = 1;
                }
              }
            }
            if ((l == 0) && (g == 1)) {
              if  (!(Character.isDigit(my_line_text.charAt(c)))) {
                okok = 1;
              }
            }
          }

          if ((okok == 0) || (okokok > 0)) {
            for (y = (s.lastIndexOf("(") + 1); y < s.lastIndexOf(")"); y++) {
              if (!(Character.isDigit(s.charAt(y)))) return false;
            }
            return true;
          }
          return false;
        }
    }
    return false;
  }
}
