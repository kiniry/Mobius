/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions.ast;

import org.apache.bcel.generic.ACONST_NULL;
import org.apache.bcel.generic.ARETURN;
import org.apache.bcel.generic.ARRAYLENGTH;
import org.apache.bcel.generic.ATHROW;
import org.apache.bcel.generic.DRETURN;
import org.apache.bcel.generic.DUP;
import org.apache.bcel.generic.DUP2;
import org.apache.bcel.generic.DUP2_X1;
import org.apache.bcel.generic.DUP2_X2;
import org.apache.bcel.generic.DUP_X1;
import org.apache.bcel.generic.DUP_X2;
import org.apache.bcel.generic.FRETURN;
import org.apache.bcel.generic.IRETURN;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.LRETURN;
import org.apache.bcel.generic.MONITORENTER;
import org.apache.bcel.generic.MONITOREXIT;
import org.apache.bcel.generic.POP;
import org.apache.bcel.generic.POP2;
import org.apache.bcel.generic.RETURN;
import org.apache.bcel.generic.SWAP;

import umbra.instructions.InstructionParser;
import umbra.lib.BytecodeStrings;


/**
 * This class handles the creation and correctness for certain instructions
 * with no parameters. The instructions handled here are in the following
 * categories:
 * <ul>
 *    <li>pushing the const null value on the top of the operand stack,</li>
 *    <li>array specific instructions,</li>
 *    <li>monitor instructions,</li>
 *    <li>return instructions,</li>
 *    <li>dup instructions,</li>
 *    <li>instructions to manipulate the top of the operand stack.</li>
 * </ul>
 *
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class SingleInstruction extends InstructionLineController {

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
  public /*@ pure @*/ SingleInstruction(final String a_line_text,
                                        final String a_name) {
    super(a_line_text, a_name);
  }

  /**
   * This method returns the array of mnemonics for instructions with no
   * parameters.
   *
   * @return the array of the handled mnemonics
   * @see InstructionLineController#getMnemonics()
   */
  public static /*@ non_null @*/ String[] getMnemonics() {
    return BytecodeStrings.SINGLE_INS;
  }

  /**
   * This method, based on the value of the the mnemonic
   * name, creates a new BCEL instruction
   * object for an instruction with no parameters. The method can construct
   * an instruction from one of the following families:
   * <ul>
   *    <li>pushing the const null value on the top of the operand stack,</li>
   *    <li>array specific instructions,</li>
   *    <li>monitor instructions,</li>
   *    <li>return instructions,</li>
   *    <li>dup instructions,</li>
   *    <li>instructions to manipulate the top of the operand stack.</li>
   * </ul>
   * This method also checks the syntactical correctness of the current
   * instruction line.
   *
   * @return the freshly constructed BCEL instruction or <code>null</code>
   *         in case the instruction is not a stack instruction and
   *         in case the instruction line is incorrect
   * @see BytecodeLineController#getInstruction()
   */
  public Instruction getInstruction() {
    if (!correct())
      return null;
    Instruction res = null;
    if (getName().compareTo("aconst_null") == 0)
      res = new ACONST_NULL();
    res = getArrayInstruction(res);
    res = getMonitorInstruction(res);
    res = getReturnInstruction(res);
    res = getDupInstruction(res);
    res = getTopManipulationInstruction(res);
    return res;
  }

  /**
   * This method creates the objects that represent instructions that
   * manipulate the top of the operand stack. It checks if the name of the
   * current instruction is one of these and in that case creates an
   * appropriate object. In case the name is of a different kind it returns
   * the parameter <code>a_res</code>.
   *
   * The instructions that manipulate the top of the operand stack are:
   * <ul>
   *    <li>pop,</li>
   *    <li>pop2,</li>
   *    <li>swap.</li>
   * </ul>
   *
   * @param a_res a helper value returned in case the current instruction is
   *   not in the current set
   * @return the object that represents the current instruction or res in
   *   case the current instruction is not in the current set
   */
  private /*@ pure @*/ Instruction getTopManipulationInstruction(
                             final /*@ nullable @*/ Instruction a_res) {
    Instruction ires = a_res;
    if (getName().compareTo("pop") == 0)
      ires = new POP();
    if (getName().compareTo("pop2") == 0)
      ires = new POP2();
    if (getName().compareTo("swap") == 0)
      ires = new SWAP();
    return ires;
  }

  /**
   * This method creates the objects that represent monitor instructions.
   * It checks if the name of the current instruction is one of these and in
   * that case creates an appropriate object. In case the name is of a different
   * kind it returns the parameter <code>a_res</code>.
   *
   * The monitor instructions are:
   * <ul>
   *    <li>monitorenter,</li>
   *    <li>monitorexit.</li>
   * </ul>
   *
   * @param a_res a helper value returned in case the current instruction is
   *   not in the current set
   * @return the object that represents the current instruction or res in
   *   case the current instruction is not in the current set
   */
  private /*@ pure @*/ Instruction getMonitorInstruction(
                             final /*@ nullable @*/ Instruction a_res) {
    Instruction ires = a_res;
    if (getName().compareTo("monitorenter") == 0)
      ires = new MONITORENTER();
    if (getName().compareTo("monitorexit") == 0)
      ires = new MONITOREXIT();
    return ires;
  }

  /**
   * This method creates the objects that represent array instructions.
   * It checks if the name of the current instruction is one of these and in
   * that case creates an appropriate object. In case the name is of a different
   * kind it returns the parameter <code>a_res</code>.
   *
   * The array instructions are:
   * <ul>
   *    <li>arraylength.</li>
   * </ul>
   *
   * @param a_res a helper value returned in case the current instruction is
   *   not in the current set
   * @return the object that represents the current instruction or res in
   *   case the current instruction is not in the current set
   */
  private /*@ pure @*/ Instruction getArrayInstruction(
                             final /*@ nullable @*/ Instruction a_res) {
    Instruction ires = a_res;
    if (getName().compareTo("arraylength") == 0)
      ires = new ARRAYLENGTH();
    return ires;
  }

  /**
   * This method creates the objects that represent dup instructions.
   * It checks if the name of the current instruction is one of these and in
   * that case creates an appropriate object. In case the name is of a different
   * kind it returns the parameter <code>a_res</code>.
   *
   * The dup instructions are:
   * <ul>
   *    <li>dup,</li>
   *    <li>dup_x1,</li>
   *    <li>dup_x2,</li>
   *    <li>dup2,</li>
   *    <li>dup2_x1,</li>
   *    <li>dup2_x2.</li>
   * </ul>
   *
   * @param a_res a helper value returned in case the current instruction is
   *   not in the current set
   * @return the object that represents the current instruction or res in
   *   case the current instruction is not in the current set
   */
  private /*@ pure @*/ Instruction getDupInstruction(
                             final /*@ nullable @*/ Instruction a_res) {
    Instruction ires = a_res;
    if (getName().compareTo("dup") == 0)
      ires = new DUP();
    if (getName().compareTo("dup_x1") == 0)
      ires = new DUP_X1();
    if (getName().compareTo("dup_x2") == 0)
      ires = new DUP_X2();
    if (getName().compareTo("dup2") == 0)
      ires = new DUP2();
    if (getName().compareTo("dup2_x1") == 0)
      ires = new DUP2_X1();
    if (getName().compareTo("dup2_x2") == 0)
      ires = new DUP2_X2();
    return ires;
  }

  /**
   * This method creates the objects that represent return instructions.
   * It checks if the name of the current instruction is one of these and in
   * that case creates an appropriate object. In case the name is of a different
   * kind it returns the parameter <code>a_res</code>.
   *
   * The return instructions are:
   * <ul>
   *    <li>areturn,</li>
   *    <li>dreturn,</li>
   *    <li>freturn,</li>
   *    <li>ireturn,</li>
   *    <li>lreturn,</li>
   *    <li>rreturn,</li>
   *    <li>athrow.</li>
   * </ul>
   *
   * @param a_res a helper value returned in case the current instruction is
   *   not in the current set
   * @return the object that represents the current instruction or res in
   *   case the current instruction is not in the current set
   */
  private /*@ pure @*/ Instruction getReturnInstruction(
                             final /*@ nullable @*/ Instruction a_res) {
    Instruction ires = a_res;
    if (getName().compareTo("areturn") == 0)
      ires = new ARETURN();
    if (getName().compareTo("dreturn") == 0)
      ires = new DRETURN();
    if (getName().compareTo("freturn") == 0)
      ires = new FRETURN();
    if (getName().compareTo("ireturn") == 0)
      ires = new IRETURN();
    if (getName().compareTo("lreturn") == 0)
      ires = new LRETURN();
    if (getName().compareTo("return") == 0)
      ires = new RETURN();
    if (getName().compareTo("athrow") == 0)
      ires = new ATHROW();
    return ires;
  }

  /*@ requires 0 <= max;
    @ ensures -1 <= \result && \result <= max && a_name.contains("_");
    @*/
  /**
   * This method extracts the number from an instruction with the constant
   * embedded in the instruction name (e.g. iload_0). This method additionally
   * checks if the number does not exceed the allowed range (between 0 and
   * <code>max</code>).
   *
   * @param a_name the name of the instruction
   * @param the_max the maximal acceptable value of the constant
   * @return the number, -1 in case the number cannot be extracted from the
   *   given name
   */
  protected static int extractConstNumber(
                  /*@ non_null @*/ final String a_name, final int the_max) {
    if (!a_name.contains("_")) {
      return -1;
    }
    try {
      final String tail = a_name.substring(a_name.indexOf('_') + 1);
      int num = Integer.parseInt(tail);
      if (!(0 <= num && num <= the_max))
        num = -1;
      return num;
    } catch (NumberFormatException e) {
      return -1;
    }
  }

  /*@ requires a_name.contains("_");
    @
    @*/
  /**
   * This method extracts the name from an instruction with the constant
   * embedded in the instruction name (e.g. iload_0). This method assumes
   * that all the sanity checks are done with the help of the method
   * {@link #extractConstNumber(String, int)}
   *
   * @param a_name the string with the instruction name (e.g. iload_0)
   * @return the text of the instruction name (e.g. iload for iload_0)
   */
  protected static /*@ non_null @*/ String extractInsName(
                                      final /*@ non_null @*/ String a_name) {
    return a_name.substring(0, a_name.indexOf('_'));
  }


  /**
   * Simple instruction line is correct if it has no parameter. That means this
   * must have the form:
   *   whitespase number : whitespace mnemonic whitespace lineend
   * where mnemonic comes from {@link BytecodeStrings#SINGLE_INS}.
   *
   * @return <code>true</code> when the instruction mnemonic is the only text
   *         in the line of the instruction text
   * @see InstructionLineController#correct()
   */
  public boolean correct() {
    return correct(BytecodeStrings.SINGLE_INS);
  }

  /**
   * This method checks the correctness of the current instruction line and if
   * the mnemonic occurs in our inventory of known mnemonics.
   *
   * The instruction line is correct when it has the form:
   *   whitespase number : whitespace mnemonic whitespace lineend
   * where mnemonic comes from {@code an_inventory}.
   *
   * @param an_inventory an array with all the correct mnemonics
   * @return <code>true</code> when the instruction mnemonic is the only text
   *         in the line of the instruction text
   * @see InstructionLineController#correct()
   */
  protected final boolean correct(final String[] an_inventory) {
    boolean res = true;
    final InstructionParser parser = getParser();
    res = parseTillMnemonic(); //parse up to mnemonic
    res = res && (parser.swallowMnemonic(an_inventory) >= 0); //mnemonic
    res = res && !parser.swallowWhitespace(); //final whitespace
    return res;
  }
}
