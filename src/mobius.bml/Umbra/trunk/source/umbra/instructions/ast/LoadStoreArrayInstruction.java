/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions.ast;

import org.apache.bcel.generic.AALOAD;
import org.apache.bcel.generic.AASTORE;
import org.apache.bcel.generic.BALOAD;
import org.apache.bcel.generic.BASTORE;
import org.apache.bcel.generic.CALOAD;
import org.apache.bcel.generic.CASTORE;
import org.apache.bcel.generic.DALOAD;
import org.apache.bcel.generic.DASTORE;
import org.apache.bcel.generic.FALOAD;
import org.apache.bcel.generic.FASTORE;
import org.apache.bcel.generic.IALOAD;
import org.apache.bcel.generic.IASTORE;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.LALOAD;
import org.apache.bcel.generic.LASTORE;
import org.apache.bcel.generic.SALOAD;
import org.apache.bcel.generic.SASTORE;

import umbra.lib.BytecodeStrings;

/**
 * This class handles the creation and correctness for certain instructions
 * with no parameters. The instructions handled here are the instructions that
 * load and store the contents of arrays.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class LoadStoreArrayInstruction extends SingleInstruction {

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
  public /*@ pure @*/ LoadStoreArrayInstruction(final String a_line_text,
                                        final String a_name) {
    super(a_line_text, a_name);
  }

  /**
   * This method returns the array of load-store instructions mnemonics for
   * arrays.
   *
   * @return the array of the handled mnemonics
   * @see InstructionLineController#getMnemonics()
   */
  public static /*@ non_null @*/ String[] getMnemonics() {
    return BytecodeStrings.LOAD_STORE_ARRAY_INS;
  }

  /**
   * This method creates the objects that represent array load or store
   * instructions. It checks if the name of the current instruction is one of
   * these and in that case creates an appropriate object. In case the name is
   * of a different kind it returns the parameter <code>a_res</code>.
   *
   * The array load or store instructions are:
   * <ul>
   *    <li>instructions to l/s arrays,</li>
   *    <li>instructions to l/s bytes,</li>
   *    <li>instructions to l/s chars,</li>
   *    <li>instructions to l/s doubles,</li>
   *    <li>instructions to l/s floats,</li>
   *    <li>instructions to l/s ints,</li>
   *    <li>instructions to l/s longs,</li>
   *    <li>instructions to l/s shorts.</li>
   * </ul>
   *
   * @param a_res a helper value returned in case the current instruction is
   *   not in the current set
   * @return the object that represents the current instruction or res in
   *   case the current instruction is not in the current set
   */
  private /*@ pure @*/ Instruction getArrayLoadStoreInstruction(
                             final /*@ nullable @*/ Instruction a_res) {
    Instruction ires = a_res;
    ires = getArrayArrayLSInstruction(ires);
    ires = getArrayBoolLSInstruction(ires);
    ires = getArrayCharLSInstruction(ires);
    ires = getArrayDoubleLSInstruction(ires);
    ires = getArrayFloatLSInstruction(ires);
    ires = getArrayIntLSInstruction(ires);
    ires = getArrayLongLSInstruction(ires);
    ires = getArrayShortLAInstruction(ires);
    return ires;
  }

  /**
   * This method creates the objects that represent array load or store
   * instructions for shorts. It checks if the name of the current instruction
   * is one of these and in that case creates an appropriate object. In case the
   * name is of a different kind it returns the parameter <code>a_res</code>.
   *
   * The array load or store instructions for shorts are:
   * <ul>
   *    <li>saload,</li>
   *    <li>sastore.</li>
   * </ul>
   *
   * @param a_res a helper value returned in case the current instruction is
   *   not in the current set
   * @return the object that represents the current instruction or res in
   *   case the current instruction is not in the current set
   */
  private Instruction getArrayShortLAInstruction(final Instruction a_res) {
    Instruction ires = a_res;
    if (getName().compareTo("saload") == 0)
      ires = new SALOAD();
    if (getName().compareTo("sastore") == 0)
      ires = new SASTORE();
    return ires;
  }

  /**
   * This method creates the objects that represent array load or store
   * instructions for longs. It checks if the name of the current instruction
   * is one of these and in that case creates an appropriate object. In case
   * the name is of a different kind it returns the parameter
   * <code>a_res</code>.
   *
   * The array load or store instructions for loads are:
   * <ul>
   *    <li>laload,</li>
   *    <li>lastore.</li>
   * </ul>
   *
   * @param a_res a helper value returned in case the current instruction is
   *   not in the current set
   * @return the object that represents the current instruction or res in
   *   case the current instruction is not in the current set
   */
  private Instruction getArrayLongLSInstruction(final Instruction a_res) {
    Instruction ires = a_res;
    if (getName().compareTo("laload") == 0)
      ires = new LALOAD();
    if (getName().compareTo("lastore") == 0)
      ires = new LASTORE();
    return ires;
  }

  /**
   * This method creates the objects that represent array load or store
   * instructions for ints. It checks if the name of the current instruction is
   * one of these and in that case creates an appropriate object. In case the
   * name is of a different kind it returns the parameter <code>a_res</code>.
   *
   * The array load or store instructions for ints are:
   * <ul>
   *    <li>iaload,</li>
   *    <li>iastore.</li>
   * </ul>
   *
   * @param a_res a helper value returned in case the current instruction is
   *   not in the current set
   * @return the object that represents the current instruction or res in
   *   case the current instruction is not in the current set
   */
  private Instruction getArrayIntLSInstruction(final Instruction a_res) {
    Instruction ires = a_res;
    if (getName().compareTo("iaload") == 0)
      ires = new IALOAD();
    if (getName().compareTo("iastore") == 0)
      ires = new IASTORE();
    return ires;
  }

  /**
   * This method creates the objects that represent array load or store
   * instructions for floats. It checks if the name of the current instruction
   * is one of these and in that case creates an appropriate object. In case the
   * name is of a different kind it returns the parameter <code>a_res</code>.
   *
   * The array load or store instructions for floats are:
   * <ul>
   *    <li>faload,</li>
   *    <li>fastore.</li>
   * </ul>
   *
   * @param a_res a helper value returned in case the current instruction is
   *   not in the current set
   * @return the object that represents the current instruction or res in
   *   case the current instruction is not in the current set
   */
  private Instruction getArrayFloatLSInstruction(final Instruction a_res) {
    Instruction ires = a_res;
    if (getName().compareTo("faload") == 0)
      ires = new FALOAD();
    if (getName().compareTo("fastore") == 0)
      ires = new FASTORE();
    return ires;
  }

  /**
   * This method creates the objects that represent array load or store
   * instructions for doubles. It checks if the name of the current instruction
   * is one of these and in that case creates an appropriate object. In case the
   * name is of a different kind it returns the parameter <code>a_res</code>.
   *
   * The array load or store instructions for doubles are:
   * <ul>
   *    <li>daload,</li>
   *    <li>dastore.</li>
   * </ul>
   *
   * @param a_res a helper value returned in case the current instruction is
   *   not in the current set
   * @return the object that represents the current instruction or res in
   *   case the current instruction is not in the current set
   */
  private Instruction getArrayDoubleLSInstruction(final Instruction a_res) {
    Instruction ires = a_res;
    if (getName().compareTo("daload") == 0)
      ires = new DALOAD();
    if (getName().compareTo("dastore") == 0)
      ires = new DASTORE();
    return ires;
  }

  /**
   * This method creates the objects that represent array load or store
   * instructions for chars. It checks if the name of the current instruction is
   * one of these and in that case creates an appropriate object. In case the
   * name is of a different kind it returns the parameter <code>a_res</code>.
   *
   * The array load or store instructions for chars are:
   * <ul>
   *    <li>caload,</li>
   *    <li>castore.</li>
   * </ul>
   *
   * @param a_res a helper value returned in case the current instruction is
   *   not in the current set
   * @return the object that represents the current instruction or res in
   *   case the current instruction is not in the current set
   */
  private Instruction getArrayCharLSInstruction(final Instruction a_res) {
    Instruction ires = a_res;
    if (getName().compareTo("caload") == 0)
      ires = new CALOAD();
    if (getName().compareTo("castore") == 0)
      ires = new CASTORE();
    return ires;
  }

  /**
   * This method creates the objects that represent array load or store
   * instructions for bytes. It checks if the name of the current instruction is
   * one of these and in that case creates an appropriate object. In case the
   * name is of a different kind it returns the parameter <code>a_res</code>.
   *
   * The array load or store instructions for bytes are:
   * <ul>
   *    <li>baload,</li>
   *    <li>bastore.</li>
   * </ul>
   *
   * @param a_res a helper value returned in case the current instruction is
   *   not in the current set
   * @return the object that represents the current instruction or res in
   *   case the current instruction is not in the current set
   */
  private Instruction getArrayBoolLSInstruction(final Instruction a_res) {
    Instruction ires = a_res;
    if (getName().compareTo("baload") == 0)
      ires = new BALOAD();
    if (getName().compareTo("bastore") == 0)
      ires = new BASTORE();
    return ires;
  }

  /**
   * This method creates the objects that represent array load or store
   * instructions for arrays. It checks if the name of the current instruction
   * is one of these and in that case creates an appropriate object. In case
   * the name is of a different kind it returns the parameter
   * <code>a_res</code>.
   *
   * The array load or store instructions for arrays are:
   * <ul>
   *    <li>aaload,</li>
   *    <li>aastore.</li>
   * </ul>
   *
   * @param a_res a helper value returned in case the current instruction is
   *   not in the current set
   * @return the object that represents the current instruction or res in
   *   case the current instruction is not in the current set
   */
  private Instruction getArrayArrayLSInstruction(final Instruction a_res) {
    Instruction ires = a_res;
    if (getName().compareTo("aaload") == 0)
      ires = new AALOAD();
    if (getName().compareTo("aastore") == 0)
      ires = new AASTORE();
    return ires;
  }


  /**
   * This method, based on the value of the the mnemonic
   * name, creates a new BCEL instruction
   * object for an instruction with no parameters that loads or stores a
   * for array entries.
   *
   * This method also checks the syntactical correctness of the current
   * instruction line.
   *
   * @return the freshly constructed BCEL instruction or <code>null</code>
   *         in case the instruction is not a instruction from the current set
   *         and in case the instruction line is incorrect
   * @see BytecodeLineController#getInstruction()
   */
  public final Instruction getInstruction() {
    if (!correct())
      return null;
    Instruction res = null;
    res = getArrayLoadStoreInstruction(res);
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
    return correct(BytecodeStrings.LOAD_STORE_ARRAY_INS);
  }
}
