/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions.ast;

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

import umbra.lib.BytecodeStrings;

/**
 * This class handles the creation and correctness for instructions
 * with no parameters that perform loading and storing data on/from the
 * operand stack. The instructions handled here are in the following
 * form:
 * <ul>
 *    <li>xload_&lt;num&gt;,</li>
 *    <li>xstore_&lt;num&gt;.</li>
 * </ul>
 * where x is one of a, c, d, f l.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class LoadStoreConstInstruction extends SingleInstruction {

  /**
   * The constant that represents the maximal value of the constant parameter
   * for instructions such as iload_&lt;n&gt;,
   * see {@link #getConstLoadStoreInstruction(Instruction)} for the full
   * inventory.
   */
  private static final int MAX_LOAD_STORE_NUM = 3;

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
  public /*@ pure @*/ LoadStoreConstInstruction(final String a_line_text,
                                   final String a_name) {
    super(a_line_text, a_name);
  }

  /**
   * This method returns the array of load and store instructions mnemonics.
   *
   * @return the array of the handled mnemonics
   * @see InstructionLineController#getMnemonics()
   */
  public static /*@ non_null @*/ String[] getMnemonics() {
    return BytecodeStrings.LOAD_STORE_INS;
  }

  /**
   * This method creates the objects that represent instructions that load
   * or store numbers and are parametrised by constants (e.g. iload_0).
   * It checks if the name of the current instruction is one of these and in
   * that case creates an appropriate object. In case the name is of a different
   * kind it returns the parameter <code>a_res</code>.
   *
   * The load or store instructions that are parametrised by constants are:
   * <ul>
   *    <li>aload_[0-3],</li>
   *    <li>astore_[0-3],</li>
   *    <li>dload_[0-3],</li>
   *    <li>dstore_[0-3],</li>
   *    <li>fload_[0-3],</li>
   *    <li>fstore_[0-3],</li>
   *    <li>iload_[0-3],</li>
   *    <li>istore_[0-3],</li>
   *    <li>lload_[0-3],</li>
   *    <li>lstore_[0-3].</li>
   * </ul>
   *
   * @param a_res a helper value returned in case the current instruction is
   *   not in the current set
   * @return the object that represents the current instruction or res in
   *   case the current instruction is not in the current set
   */
  private /*@ pure @*/ Instruction getConstLoadStoreInstruction(
                             final /*@ nullable @*/ Instruction a_res) {
    Instruction ires = a_res;
    final int num = extractConstNumber(getName(), MAX_LOAD_STORE_NUM);
    if (num >= 0) {
      final String iName = extractInsName(getName());
      ires = getALSInstruction(ires, num, iName);
      ires = getDLSInstruction(ires, num, iName);
      ires = getFLSInstruction(ires, num, iName);
      ires = getILSInstruction(ires, num, iName);
      ires = getLLSInstruction(ires, num, iName);
    } else {
      return ires;
    }
    return ires;
  }

  /*@ requires 0 <= num && num <= MAX_LOAD_STORE_NUM;
    @ ensures a_res != null ==> \result == a_res;
    @*/
  /**
   * This method creates the objects that represent instructions that load
   * or store long numbers and are parametrised by constants (e.g. lload_0).
   * It assumes all the checks are done in
   * {@link #getConstLoadStoreInstruction(Instruction)}.
   * In case the name mentioned in <code>a_name</code> is of a different kind it
   * returns the parameter <code>a_res</code>.
   *
   * The load or store instructions for longs that are parametrised by constants
   * are:
   * <ul>
   *    <li>lload_[0-3],</li>
   *    <li>lstore_[0-3].</li>
   * </ul>
   *
   * @param a_res a helper value returned in case the current instruction is
   *   not in the current set
   * @param a_num the number constant with which the instruction should be
   *   created
   * @param a_name the name of the instruction (with the number stripped,
   *   e.g. for lload_0 it is lload)
   * @return the object that represents the current instruction or res in
   *   case the current instruction is not in the current set
   */
  private /*@ pure @*/ Instruction getLLSInstruction(
                final /*@ nullable @*/ Instruction a_res,
                final int a_num,
                final /*@ non_null @*/ String a_name) {
    Instruction ires = a_res;
    if (a_name.equals("lload")) {
      ires = new LLOAD(a_num);
    } else if (a_name.equals("lstore")) {
      ires = new LSTORE(a_num);
    }
    return ires;
  }

  /*@ requires 0 <= num && num <= MAX_LOAD_STORE_NUM;
    @ ensures a_res != null ==> \result == a_res;
    @*/
  /**
   * This method creates the objects that represent instructions that load
   * or store int numbers and are parametrised by constants (e.g. iload_0).
   * It assumes all the checks are done in
   * {@link #getConstLoadStoreInstruction(Instruction)}.
   * In case the name mentioned in <code>a_name</code> is of a different kind it
   * returns the parameter <code>a_res</code>.
   *
   * The load or store instructions for ints that are parametrised by constants
   * are:
   * <ul>
   *    <li>iload_[0-3],</li>
   *    <li>istore_[0-3].</li>
   * </ul>
   *
   * @param a_res a helper value returned in case the current instruction is
   *  not in the current set
   * @param a_num the number constant with which the instruction should be
   *   created
   * @param a_name the name of the instruction (with the number stripped,
   *   e.g. for iload_0 it is iload)
   * @return the object that represents the current instruction or res in
   *  case the current instruction is not in the current set
   */
  private Instruction getILSInstruction(
                final /*@ nullable @*/ Instruction a_res,
                final int a_num,
                final /*@ non_null @*/ String a_name) {
    Instruction ires = a_res;
    if (a_name.equals("iload")) {
      ires = new ILOAD(a_num);
    } else if (a_name.equals("istore")) {
      ires = new ISTORE(a_num);
    }
    return ires;
  }

  /*@ requires 0 <= num && num <= MAX_LOAD_STORE_NUM;
    @ ensures a_res != null ==> \result == a_res;
    @*/
  /**
   * This method creates the objects that represent instructions that load
   * or store float numbers and are parametrised by constants (e.g. fload_0).
   * It assumes all the checks are done in
   * {@link #getConstLoadStoreInstruction(Instruction)}.
   * In case the name mentioned in <code>a_name</code> is of a different kind it
   * returns the parameter <code>a_res</code>.
   *
   * The load or store instructions for floats that are parametrised by
   * constants are:
   * <ul>
   *    <li>fload_[0-3],</li>
   *    <li>fstore_[0-3].</li>
   * </ul>
   *
   * @param a_res a helper value returned in case the current instruction is
   *   not in the current set
   * @param a_num the number constant with which the instruction should be
   *  created
   * @param a_name the name of the instruction (with the number stripped,
   *   e.g. for fload_0 it is fload)
   * @return the object that represents the current instruction or res in
   *   case the current instruction is not in the current set
   */
  private Instruction getFLSInstruction(
                final Instruction a_res,
                final int a_num,
                final String a_name) {
    Instruction ires = a_res;
    if (a_name.equals("fload")) {
      ires = new FLOAD(a_num);
    } else if (a_name.equals("fstore")) {
      ires = new FSTORE(a_num);
    }
    return ires;
  }

  /*@ requires 0 <= num && num <= MAX_LOAD_STORE_NUM;
    @ ensures a_res != null ==> \result == a_res;
    @*/
  /**
   * This method creates the objects that represent instructions that load
   * or store double numbers and are parametrised by constants (e.g. dload_0).
   * It assumes all the checks are done in
   * {@link #getConstLoadStoreInstruction(Instruction)}.
   * In case the name mentioned in <code>a_name</code> is of a different kind it
   * returns the parameter <code>a_res</code>.
   *
   * The load or store instructions for doubles that are parametrised by
   * constants are:
   * <ul>
   *    <li>dload_[0-3],</li>
   *    <li>dstore_[0-3].</li>
   * </ul>
   *
   * @param a_res a helper value returned in case the current instruction is
   *   not in the current set
   * @param a_num the number constant with which the instruction should be
   *   created
   * @param a_name the name of the instruction (with the number stripped,
   *   e.g. for dload_0 it is dload)
   * @return the object that represents the current instruction or res in
   *   case the current instruction is not in the current set
   */
  private Instruction getDLSInstruction(
                final Instruction a_res,
                final int a_num,
                final String a_name) {
    Instruction ires = a_res;
    if (a_name.equals("dload")) {
      ires = new DLOAD(a_num);
    } else if (a_name.equals("dstore")) {
      ires = new DSTORE(a_num);
    }
    return ires;
  }

  /*@ requires 0 <= num && num <= MAX_LOAD_STORE_NUM;
    @ ensures a_res != null ==> \result == a_res;
    @*/
  /**
   * This method creates the objects that represent instructions that load
   * or store references and are parametrised by constants (e.g. aload_0).
   * It assumes all the checks are done in
   * {@link #getConstLoadStoreInstruction(Instruction)}.
   * In case the name mentioned in <code>a_name</code> is of a different kind it
   * returns the parameter <code>a_res</code>.
   *
   * The load or store instructions for references that are parametrised by
   * constants are:
   * <ul>
   *    <li>aload_[0-3],</li>
   *    <li>astore_[0-3].</li>
   * </ul>
   *
   * @param a_res a helper value returned in case the current instruction is
   *   not in the current set
   * @param a_num the number constant with which the instruction should be
   *   created
   * @param a_name the name of the instruction (with the number stripped,
   *   e.g. for lload_0 it is lload)
   * @return the object that represents the current instruction or res in
   *   case the current instruction is not in the current set
   */
  private Instruction getALSInstruction(
                final Instruction a_res,
                final int a_num,
                final String a_name) {
    Instruction ires = a_res;
    if (a_name.equals("aload")) {
      ires = new ALOAD(a_num);
    } else if (a_name.equals("astore")) {
      ires = new ASTORE(a_num);
    }
    return ires;
  }

  /**
   * This method, based on the value of the instruction line (from
   * {@link InstructionLineController}), creates a new BCEL instruction
   * object for an instruction with no parameters that loads or stores a
   * for a constant value i.e.
   * <ul>
   *    <li>xload_&lt;number&gt;,</li>
   *    <li>xstore_&lt;number&gt;.</li>
   * </ul>
   * where x is one of a, c, d, f l.
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
    res = getConstLoadStoreInstruction(res);
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
    return correct(BytecodeStrings.LOAD_STORE_INS);
  }
}
