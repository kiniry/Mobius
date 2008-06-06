/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions.ast;

import org.apache.bcel.generic.DADD;
import org.apache.bcel.generic.DDIV;
import org.apache.bcel.generic.DMUL;
import org.apache.bcel.generic.DNEG;
import org.apache.bcel.generic.DREM;
import org.apache.bcel.generic.DSUB;
import org.apache.bcel.generic.FADD;
import org.apache.bcel.generic.FDIV;
import org.apache.bcel.generic.FMUL;
import org.apache.bcel.generic.FNEG;
import org.apache.bcel.generic.FREM;
import org.apache.bcel.generic.FSUB;
import org.apache.bcel.generic.IADD;
import org.apache.bcel.generic.IAND;
import org.apache.bcel.generic.IDIV;
import org.apache.bcel.generic.IMUL;
import org.apache.bcel.generic.INEG;
import org.apache.bcel.generic.IOR;
import org.apache.bcel.generic.IREM;
import org.apache.bcel.generic.ISHL;
import org.apache.bcel.generic.ISUB;
import org.apache.bcel.generic.IUSHR;
import org.apache.bcel.generic.IXOR;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.LADD;
import org.apache.bcel.generic.LAND;
import org.apache.bcel.generic.LCMP;
import org.apache.bcel.generic.LDIV;
import org.apache.bcel.generic.LMUL;
import org.apache.bcel.generic.LNEG;
import org.apache.bcel.generic.LOR;
import org.apache.bcel.generic.LREM;
import org.apache.bcel.generic.LSHL;
import org.apache.bcel.generic.LSHR;
import org.apache.bcel.generic.LSUB;
import org.apache.bcel.generic.LUSHR;
import org.apache.bcel.generic.LXOR;

import umbra.lib.BytecodeStrings;

/**
 * This class handles the creation and correctness for arithmetic instructions
 * with no parameters. The instructions handled here are in the following
 * categories:
 * <ul>
   *    <li>arithmetic instructions for doubles,</li>
   *    <li>arithmetic instructions for floats,</li>
   *    <li>arithmetic instructions for integers, and</li>
   *    <li>arithmetic instructions for longs.</li>
 * </ul>
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class ArithmeticInstruction extends SingleInstruction {


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
  public /*@ pure @*/ ArithmeticInstruction(final String a_line_text,
                                            final String a_name) {
    super(a_line_text, a_name);
  }

  /**
   * This method returns the array of arithmetic instructions mnemonics.
   *
   * @return the array of the handled mnemonics
   * @see InstructionLineController#getMnemonics()
   */
  public static /*@ non_null @*/ String[] getMnemonics() {
    return BytecodeStrings.ARITHMETIC_INS;
  }

  /**
   * This method creates the objects that represent instructions which perform
   * arithmetic operations on longs. It checks if the name of the current
   * instruction is one of these and in that case creates an appropriate object.
   * In case the name is of a different kind it returns the parameter
   * <code>a_res</code>.
   *
   * The instructions which perform arithmetic operations on longs are:
   * <ul>
   *    <li>lsub,</li>
   *    <li>ladd,</li>
   *    <li>ldiv,</li>
   *    <li>lmul,</li>
   *    <li>lneg,</li>
   *    <li>lrem,</li>
   *    <li>lcmp,</li>
   *    <li>or a bit shift operations on longs,</li>
   *    <li>or boolean operations on longs.</li>
   * </ul>
   *
   * @param a_res a helper value returned in case the current instruction is
   *   not in the current set
   * @return the object that represents the current instruction or res in
   *   case the current instruction is not in the current set
   */
  private /*@ pure @*/ Instruction getLOpInstruction(
                             final /*@ nullable @*/ Instruction a_res) {
    Instruction ires = a_res;
    if (getName().compareTo("lsub") == 0)
      ires = new LSUB();
    if (getName().compareTo("ladd") == 0)
      ires = new LADD();
    if (getName().compareTo("ldiv") == 0)
      ires = new LDIV();
    if (getName().compareTo("lmul") == 0)
      ires = new LMUL();
    if (getName().compareTo("lneg") == 0)
      ires = new LNEG();
    if (getName().compareTo("lrem") == 0)
      ires = new LREM();
    if (getName().compareTo("lcmp") == 0)
      ires = new LCMP();
    ires = getLShiftOpInstruction(ires);
    ires = getLBoolOpInstruction(ires);
    return ires;
  }

  /**
   * This method creates the objects that represent instructions which perform
   * shift operations on longs. It checks if the name of the current
   * instruction is one of these and in that case creates an appropriate object.
   * In case the name is of a different kind it returns the parameter
   * <code>a_res</code>.
   *
   * The instructions which perform boolean operations on longs are:
   * <ul>
   *    <li>lshl,</li>
   *    <li>lshr,</li>
   *    <li>lushr.</li>
   * </ul>
   *
   * @param a_res a helper value returned in case the current instruction is
   *   not in the current set
   * @return the object that represents the current instruction or res in
   *   case the current instruction is not in the current set
   */
  private Instruction getLShiftOpInstruction(final Instruction a_res) {
    Instruction ires = a_res;
    if (getName().compareTo("lshl") == 0)
      ires = new LSHL();
    if (getName().compareTo("lshr") == 0)
      ires = new LSHR();
    if (getName().compareTo("lushr") == 0)
      ires = new LUSHR();
    return ires;
  }

  /**
   * This method creates the objects that represent instructions which perform
   * boolean operations on longs. It checks if the name of the current
   * instruction is one of these and in that case creates an appropriate object.
   * In case the name is of a different kind it returns the parameter
   * <code>a_res</code>.
   *
   * The instructions which perform boolean operations on longs are:
   * <ul>
   *    <li>land,</li>
   *    <li>lor,</li>
   *    <li>lxor.</li>
   * </ul>
   *
   * @param a_res a helper value returned in case the current instruction is
   *   not in the current set
   * @return the object that represents the current instruction or res in
   *   case the current instruction is not in the current set
   */
  private Instruction getLBoolOpInstruction(final Instruction a_res) {
    Instruction ires = a_res;
    if (getName().compareTo("land") == 0)
      ires = new LAND();
    if (getName().compareTo("lor") == 0)
      ires = new LOR();
    if (getName().compareTo("lxor") == 0)
      ires = new LXOR();
    return ires;
  }

  /**
   * This method creates the objects that represent instructions which perform
   * arithmetic operations on ints. It checks if the name of the current
   * instruction is one of these and in that case creates an appropriate object.
   * In case the name is of a different kind it returns the parameter
   * <code>a_res</code>.
   *
   * The instructions which perform arithmetic operations on ints are:
   * <ul>
   *    <li>isub,</li>
   *    <li>iadd,</li>
   *    <li>idiv,</li>
   *    <li>imul,</li>
   *    <li>ineg,</li>
   *    <li>irem,</li>
   *    <li>ishl,</li>
   *    <li>iushr,</li>
   *    <li>or a boolean operation on ints.</li>
   * </ul>
   *
   * @param a_res a helper value returned in case the current instruction is
   *   not in the current set
   * @return the object that represents the current instruction or res in
   *   case the current instruction is not in the current set
   */
  private /*@ pure @*/ Instruction getIOpInstruction(
                             final /*@ nullable @*/ Instruction a_res) {
    Instruction ires = a_res;
    if (getName().compareTo("isub") == 0)
      ires = new ISUB();
    if (getName().compareTo("iadd") == 0)
      ires = new IADD();
    if (getName().compareTo("idiv") == 0)
      ires = new IDIV();
    if (getName().compareTo("imul") == 0)
      ires = new IMUL();
    if (getName().compareTo("ineg") == 0)
      ires = new INEG();
    if (getName().compareTo("irem") == 0)
      ires = new IREM();
    if (getName().compareTo("ishl") == 0)
      ires = new ISHL();
    if (getName().compareTo("iushr") == 0)
      ires = new IUSHR();
    ires = getIBoolOpInstruction(ires);
    return ires;
  }

  /**
   * This method creates the objects that represent instructions which perform
   * boolean operations on ints. It checks if the name of the current
   * instruction is one of these and in that case creates an appropriate object.
   * In case the name is of a different kind it returns the parameter
   * <code>a_res</code>.
   *
   * The instructions which perform boolean operations on ints are:
   * <ul>
   *    <li>iand,</li>
   *    <li>ior,</li>
   *    <li>ixor.</li>
   * </ul>
   *
   * @param a_res a helper value returned in case the current instruction is
   *   not in the current set
   * @return the object that represents the current instruction or res in
   *   case the current instruction is not in the current set
   */
  private Instruction getIBoolOpInstruction(final Instruction a_res) {
    Instruction ires = a_res;
    if (getName().compareTo("iand") == 0)
      ires = new IAND();
    if (getName().compareTo("ior") == 0)
      ires = new IOR();
    if (getName().compareTo("ixor") == 0)
      ires = new IXOR();
    return ires;
  }

  /**
   * This method creates the objects that represent instructions which perform
   * arithmetic operations on floats. It checks if the name of the current
   * instruction is one of these and in that case creates an appropriate object.
   * In case the name is of a different kind it returns the parameter
   * <code>a_res</code>.
   *
   * The instructions which perform arithmetic operations on floats are:
   * <ul>
   *    <li>fsub,</li>
   *    <li>fadd,</li>
   *    <li>fdiv,</li>
   *    <li>fmul,</li>
   *    <li>fneg,</li>
   *    <li>frem.</li>
   * </ul>
   *
   * @param a_res a helper value returned in case the current instruction is
   *   not in the current set
   * @return the object that represents the current instruction or res in
   *   case the current instruction is not in the current set
   */
  private /*@ pure @*/ Instruction getFOpInstruction(
                             final /*@ nullable @*/ Instruction a_res) {
    Instruction ires = a_res;
    if (getName().compareTo("fsub") == 0)
      ires = new FSUB();
    if (getName().compareTo("fadd") == 0)
      ires = new FADD();
    if (getName().compareTo("fdiv") == 0)
      ires = new FDIV();
    if (getName().compareTo("fmul") == 0)
      ires = new FMUL();
    if (getName().compareTo("fneg") == 0)
      ires = new FNEG();
    if (getName().compareTo("frem") == 0)
      ires = new FREM();
    return ires;
  }

  /**
   * This method creates the objects that represent instructions which perform
   * arithmetic operations on doubles. It checks if the name of the current
   * instruction is one of these and in that case creates an appropriate object.
   * In case the name is of a different kind it returns the parameter
   * <code>a_res</code>.
   *
   * The instructions which perform arithmetic operations on doubles are:
   * <ul>
   *    <li>dsub,</li>
   *    <li>dadd,</li>
   *    <li>ddiv,</li>
   *    <li>dmul,</li>
   *    <li>dneg,</li>
   *    <li>drem.</li>
   * </ul>
   *
   * @param a_res a helper value returned in case the current instruction is
   *   not in the current set
   * @return the object that represents the current instruction or res in
   *   case the current instruction is not in the current set
   */
  private /*@ pure @*/ Instruction getDOpInstruction(
                             final /*@ nullable @*/ Instruction a_res) {
    Instruction ires = a_res;
    if (getName().compareTo("dsub") == 0)
      ires = new DSUB();
    if (getName().compareTo("dadd") == 0)
      ires = new DADD();
    if (getName().compareTo("ddiv") == 0)
      ires = new DDIV();
    if (getName().compareTo("dmul") == 0)
      ires = new DMUL();
    if (getName().compareTo("dneg") == 0)
      ires = new DNEG();
    if (getName().compareTo("drem") == 0)
      ires = new DREM();
    return ires;
  }

  /**
   * This method, based on the value of the mnemonic field, creates a new BCEL
   * instruction object for an arithmetic instruction with no parameters. The
   * method can construct an instruction from one of the following families:
   * <ul>
   *    <li>arithmetic instructions for doubles,</li>
   *    <li>arithmetic instructions for floats,</li>
   *    <li>arithmetic instructions for integers, and</li>
   *    <li>arithmetic instructions for longs.</li>
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
    res = getDOpInstruction(res);
    res = getFOpInstruction(res);
    res = getIOpInstruction(res);
    res = getLOpInstruction(res);
    return res;
  }

  /**
   * Simple arithmetic instruction line is correct if it has no parameter and
   * comes from the inventory of arithmetic instructions.
   *
   * @return <code>true</code> when the instruction mnemonic is the only text
   *         in the line of the instruction text
   * @see InstructionLineController#correct()
   */
  public boolean correct() {
    return correct(BytecodeStrings.ARITHMETIC_INS);
  }
}
