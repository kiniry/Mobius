/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions;

import org.apache.bcel.generic.ALOAD;
import org.apache.bcel.generic.ASTORE;
import org.apache.bcel.generic.DLOAD;
import org.apache.bcel.generic.DSTORE;
import org.apache.bcel.generic.FLOAD;
import org.apache.bcel.generic.FSTORE;
import org.apache.bcel.generic.ILOAD;
import org.apache.bcel.generic.ISTORE;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.LLOAD;
import org.apache.bcel.generic.LSTORE;

import umbra.UmbraHelper;
import umbra.editor.parsing.BytecodeStrings;


/**
 * This class is related to some subset of instructions
 * depending on parameters. It redefines some crucial while
 * handling with single instruction methods(correctness, getting handle).
 * Load and store instrucions.
 *
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @version a-01
 */
public class StackInstruction extends NumInstruction {

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
  public StackInstruction(final String a_line_text, final String a_name) {
    super(a_line_text, a_name);
  }

  /**
   * Stack instruction line is correct if it has
   * one number parameter preceded with %.
   *
   * @return <code>true</code> when the syntax of the instruction line is
   *         correct
   * @see InstructionLineController#correct()
   */
  public final boolean correct()
  {
    String s;
    s = UmbraHelper.stripAllWhitespace(getMy_line_text());
    final String[] s2 = BytecodeStrings.STACK_INS;
    if (s.indexOf("%") < s.indexOf(":") + 1)
      return false;
    int res = 0;
    for (int j = 0; j < s2.length; j++) {
      res = checkInstructionWithNumber(s, s2[j], '%');
      if (res != 0) return res > 0;
    }
    return false;
  }


  /**
   * This method retrieves the numerical value of the index parameter of the
   * instruction in {@link BytecodeLineController#getMy_line_text()}. This
   * parameter is located after the last '%' character in the line.
   *
   * TODO this may be done simpler, and it is duplicated code
   *
   * @return the value of the numerical parameter of the instruction
   */
  private int getInd() {
    final String my_line_text = getMy_line_text();
    boolean isd;
    final String licznik = "0123456789";
    int liczba;

    isd = true;
    int dokad = my_line_text.length();
    for (int i = my_line_text.lastIndexOf("%") + 1; //XXX maybe first?
         i < my_line_text.length(); i++) {
      if (!Character.isDigit(my_line_text.charAt(i))) {
        dokad = i;
        break;
      }
    }
    if (isd) {
      liczba = 0;
      for (int i = my_line_text.lastIndexOf("%") + 1; i < dokad; i++) {
        liczba = 10 * liczba +
                              licznik.indexOf(my_line_text.substring(i, i + 1));
      }
      return liczba;
    }
    return 0;
  }

  /**
   * This method, based on the value of the field
   * {@ref InstructionLineController#my_name}, creates a new BCEL instruction
   * object for a stack instruction. It computes the index parameter of the
   * instruction before the instruction is constructed. The method can construct
   * one of the instructions:
   * <ul>
   *    <li>aload,</li>
   *    <li>astore,</li>
   *    <li>dload,</li>
   *    <li>dstore,</li>
   *    <li>fload,</li>
   *    <li>fstore,</li>
   *    <li>iload,</li>
   *    <li>istore,</li>
   *    <li>lload,</li>
   *    <li>lstore.</li>
   * </ul>
   * This method also checks the syntactical correctness of the current
   * instruction line.
   *
   * @return the freshly constructed BCEL instruction or <code>null</code>
   *         in case the instruction is not a stack instruction and
   *         in case the instruction line is incorrect
   * @see BytecodeLineController#getInstruction()
   */
  public final Instruction getInstruction() {
    int index = 0;
    Instruction res = null;
    if (!correct())
      return null;
    index = getInd();

    if (getName().compareTo("aload") == 0) {
      res = new ALOAD(index);
    }
    if (getName().compareTo("astore") == 0) {
      res = new ASTORE(index);
    }
    if (getName().compareTo("dload") == 0) {
      res = new DLOAD(index);
    }
    if (getName().compareTo("dstore") == 0) {
      res = new DSTORE(index);
    }
    if (getName().compareTo("fload") == 0) {
      res = new FLOAD(index);
    }
    if (getName().compareTo("fstore") == 0) {
      res = new FSTORE(index);
    }
    if (getName().compareTo("iload") == 0) {
      res = new ILOAD(index);
    }
    if (getName().compareTo("istore") == 0) {
      res = new ISTORE(index);
    }
    if (getName().compareTo("lload") == 0) {
      res = new LLOAD(index);
    }
    if (getName().compareTo("lstore") == 0) {
      res = new LSTORE(index);
    }

    return res;
  }
}
