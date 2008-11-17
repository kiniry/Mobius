/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions.ast;

import org.apache.bcel.generic.ICONST;
import org.apache.bcel.generic.Instruction;

import umbra.lib.BytecodeStrings;

/**
 * This class handles the creation and correctness for iconst instructions
 * with no parameters.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class IConstInstruction extends SingleInstruction {

  /**
   * The constant that represents the maximal value of the constant parameter
   * for instructions such as iconst_&lt;n&gt;,
   * see {@link #getIConstInstruction(Instruction)} for the full
   * inventory.
   */
  private static final int MAX_ICONST_NUM = 5;

  /**
   * This creates an instance of an instruction
   * named as <code>a_name</code> with the line text
   * <code>a_line</code>. Currently it just calls the constructor of the
   * superclass.
   *
   * @param a_line_text the line number of the instruction
   * @param a_name the mnemonic name of the instruction
   * @see InstructionLineController#InstructionLineController(String, String)
   */
  public /*@ pure @*/ IConstInstruction(final String a_line_text,
                                        final String a_name) {
    super(a_line_text, a_name);
  }

  /**
   * This method returns the array of iconst instructions mnemonics.
   *
   * @return the array of the handled mnemonics
   * @see InstructionLineController#getMnemonics()
   */
  public static /*@ non_null @*/ String[] getMnemonics() {
    return BytecodeStrings.ICONST_INS;
  }

  /**
   * This method creates the objects that represent iconst instructions
   * (e.g. iconst_0). It checks if the name of the current instruction is one of
   * these and in that case creates an appropriate object. In case the name is
   * of a different kind it returns the parameter <code>a_res</code>.
   *
   * @param a_res a helper value returned in case the current instruction is
   *   not in the current set
   * @return the object that represents the current instruction or res in
   *   case the current instruction is not in the current set
   */
  private /*@ pure @*/ Instruction getIConstInstruction(
                             final /*@ nullable @*/ Instruction a_res) {
    Instruction ires = a_res;
    final int num = extractConstNumber(getName(), MAX_ICONST_NUM);
    if (num >= -1) {
      final String iName = extractInsName(getName());
      if (iName.equals("iconst"))
        ires = new ICONST(num);
    } else if (getName().equals("iconst_m1")) {
      ires = new ICONST(-1);
    }
    return ires;
  }

  /**
   * This method, based on the value of the the mnemonic
   * name, creates a new BCEL instruction
   * object for an iconst instruction with no parameters. The method can
   * construct an instruction from iconst instructions only.
   *
   * This method also checks the syntactical correctness of the current
   * instruction line.
   *
   * @return the freshly constructed BCEL instruction or <code>null</code>
   *         in case the instruction is not an iconst instruction and
   *         in case the instruction line is incorrect
   * @see BytecodeLineController#getInstruction()
   */
  public Instruction getInstruction() {
    if (!correct())
      return null;
    Instruction res = null;
    res = getIConstInstruction(res);
    return res;
  }

  /**
   * Simple instruction line is correct if it has no parameter.
   *
   * @return <code>true</code> when the instruction mnemonic is the only text
   *         in the line of the instruction text
   * @see InstructionLineController#correct()
   */
  public boolean correct() {
    return correct(BytecodeStrings.ICONST_INS);
  }
}
