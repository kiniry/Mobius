/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions;

import org.apache.bcel.generic.ANEWARRAY;
import org.apache.bcel.generic.CHECKCAST;
import org.apache.bcel.generic.INSTANCEOF;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.NEW;

import umbra.UmbraHelper;
import umbra.editor.parsing.BytecodeStrings;

/**
 * This class is related to some subset of instructions
 * depending on parameters. It redefines some crucial while
 * handling with single instruction methods(correctness, getting handle).
 * This is a set of various instructions with class name
 * as a parameter.
 *
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @version a-01
 */
public class NewInstruction extends StringInstruction {

  /**
   * A position before which the '(' character cannot occur in a correct line.
   */
  private static final int LEFT_PAREN_FORBIDDEN_BOUND = 2;

  /**
   * A position before which the ')' character cannot occur in a correct line.
   */
  private static final int RIGHT_PAREN_FORBIDDEN_BOUND = 2;

  /**
   * A position before which the '<' character cannot occur in a correct line.
   */
  private static final int LESS_FORBIDDEN_BOUND = 2;

  /**
   * A position before which the '>' character cannot occur in a correct line.
   */
  private static final int GREATER_FORBIDDEN_BOUND = 2;

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
  public NewInstruction(final String a_line_text, final String a_name) {
    super(a_line_text, a_name);
  }


  /**
   * New instruction line is correct if it has
   * one parameter that is a class name and
   * another one that is a number in ().
   *
   * @return TODO
   * @see InstructionLineController#correct()
   */
  public final boolean correct() {
    final String my_line_text = getMy_line_text();
    final String s = UmbraHelper.stripAllWhitespace(my_line_text);
    final String[] s2 = BytecodeStrings.NEW_INS;
    int j, y;
    for (j = 0; j < s2.length; j++) {
      if ((s.indexOf(s2[j]) > 0) &&
          (s.indexOf(s2[j]) <= s.indexOf(":") + 1)) {
        //zakladam ze zawsze z (number)
        // w <char lub java.costam> wiec tez nie wiadomo co
        if (s.indexOf("<") < LESS_FORBIDDEN_BOUND) return false;
        if (s.indexOf(">") < GREATER_FORBIDDEN_BOUND) return false;
        //&*poprawiam
        if (s.lastIndexOf("(") < LEFT_PAREN_FORBIDDEN_BOUND) return false;
        if (s.lastIndexOf(")") < RIGHT_PAREN_FORBIDDEN_BOUND) return false;
        int m, n, o;
        m = my_line_text.lastIndexOf("(");
        n = my_line_text.lastIndexOf(")");
        if (m + 1 >= n) {
          return false;
        }
        for (o = m + 1; o < n; o++) {
          if (!(Character.isDigit(my_line_text.charAt(o)))) {
            return false;
          }
        }

        //to dziala dla wszystkich moze by tak isLetter||.
        for (y = (s.indexOf("<") + 1); y < s.indexOf(">"); y++) {
          if (!(Character.isDefined(s.charAt(y)))) return false;
        }
        return true;
      }
    }
    return false;
  }


  /**
   * This method, based on the value of the field
   * {@ref InstructionLineController#my_name}, creates a new BCEL instruction
   * object for a new-like instruction. It computes the index parameter
   * of the instruction before the instruction is constructed. The method can
   * construct one of the instructions:
   * <ul>
   *   <li>anewarray,</li>
   *   <li>checkcast,</li>
   *   <li>instanceof,</li>
   *   <li>new.</li>
   * </ul>
   * This method also checks the syntactical correctness of the current
   * instruction line.
   *
   * @return the freshly constructed BCEL instruction or <code>null</code>
   *         in case the instruction is not a new-like instruction and in case
   *         the line is incorrect
   * @see BytecodeLineController#getInstruction()
   */
  public final Instruction getInstruction() {
    int index;
    Instruction res = null;
    if (!correct())
      return null;
    index = getInd();
    if (getName().compareTo("anewarray") == 0) {
      res = new ANEWARRAY(index);
    }
    if (getName().compareTo("checkcast") == 0) {
      res = new CHECKCAST(index);
    }
    if (getName().compareTo("instanceof") == 0) {
      res = new INSTANCEOF(index);
    }
    if (getName().compareTo("new") == 0) {
      res = new NEW(index);
    }
    return res;
  }
}
