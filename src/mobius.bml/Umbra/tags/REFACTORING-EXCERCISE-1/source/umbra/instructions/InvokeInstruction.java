/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions;

import org.apache.bcel.generic.INVOKESPECIAL;
import org.apache.bcel.generic.INVOKESTATIC;
import org.apache.bcel.generic.INVOKEVIRTUAL;
import org.apache.bcel.generic.Instruction;

import umbra.UmbraHelper;
import umbra.editor.parsing.BytecodeStrings;


/**
 * This class is related to some subset of instructions
 * depending on parameters. It redefines some crucial while
 * handling with single instruction methods (correctness, getting handle).
 * Instructions of this kind are used to call other methods.
 *
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @version a-01
 */
public class InvokeInstruction extends StringInstruction {

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
  public InvokeInstruction(final String a_line_text, final String a_name) {
    super(a_line_text, a_name);
  }


  /**
   * Invoke instruction line is correct if its parameter
   * contains class name at the beginning and a number in ()
   * at the end.
   *
   * @return TODO
   * @see InstructionLineController#correct()
   */
  public final boolean correct() {
    final String my_line_text = getMy_line_text();
    final String s = UmbraHelper.stripAllWhitespace(my_line_text);
    final String[] s2 = BytecodeStrings.INVOKE_INS;
    int j;
    for (j = 0; j < s2.length; j++) {
      if ((s.indexOf(s2[j]) > 0) &&
          (s.indexOf(s2[j]) <= s.indexOf(":") + 1)) {
        if (s.lastIndexOf("(") < LEFT_PAREN_FORBIDDEN_BOUND)
          return false; //TODO is it all right
        if (s.lastIndexOf(")") < RIGHT_PAREN_FORBIDDEN_BOUND) return false;
        int m, n, o;
        m = my_line_text.lastIndexOf("(");
        n = my_line_text.lastIndexOf(")");
        if (m + 1 >= n) return false;
        for (o = m + 1; o < n; o++) {
          if (!(Character.isDigit(my_line_text.charAt(o)))) {
            return false;
          }
        }
        return true;
      }
    }
    return false;
  }

  /**
   * This method, based on the value of the field
   * {@ref InstructionLineController#my_name}, creates a new BCEL instruction
   * object for an invoke instruction. It computes the index parameter
   * of the instruction before the instruction is constructed. The method can
   * construct one of the instructions:
   * <ul>
   *   <li>invokespecial,</li>
   *   <li>invokestatic,</li>
   *   <li>invokevirtual.</li>
   * </ul>
   * This method also checks the syntactical correctness of the current
   * instruction line.
   *
   * @return the freshly constructed BCEL instruction or <code>null</code>
   *         in case the instruction is not an invoke instruction and in case
   *         the line is incorrect
   * @see BytecodeLineController#getInstruction()
   */
  public final Instruction getInstruction() {
    int index;
    index = getInd();

    if (!correct())
      return null;
    Instruction res = null;
    if (getName().compareTo("invokespecial") == 0) {
      res = new INVOKESPECIAL(index);
    }
    if (getName().compareTo("invokestatic") == 0) {
      res = new INVOKESTATIC(index);
    }
    if (getName().compareTo("invokevirtual") == 0) {
      res = new INVOKEVIRTUAL(index);
    }

    return res;

  }
}
