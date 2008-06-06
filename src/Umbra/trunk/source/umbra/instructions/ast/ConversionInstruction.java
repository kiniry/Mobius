/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */

package umbra.instructions.ast;

import org.apache.bcel.generic.D2F;
import org.apache.bcel.generic.D2I;
import org.apache.bcel.generic.D2L;
import org.apache.bcel.generic.F2D;
import org.apache.bcel.generic.F2I;
import org.apache.bcel.generic.F2L;
import org.apache.bcel.generic.I2B;
import org.apache.bcel.generic.I2C;
import org.apache.bcel.generic.I2D;
import org.apache.bcel.generic.I2F;
import org.apache.bcel.generic.I2L;
import org.apache.bcel.generic.I2S;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.L2D;
import org.apache.bcel.generic.L2F;
import org.apache.bcel.generic.L2I;

import umbra.lib.BytecodeStrings;

/**
 * This class handles the creation and correctness for the instructions
 * with no parameters which convert types. The instructions handled here are:
 * <ul>
 *    <li>conversion from doubles,</li>
 *    <li>conversion from floats,</li>
 *    <li>conversion from integers,</li>
 *    <li>conversion from longs.</li>
 * </ul>
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class ConversionInstruction extends SingleInstruction {

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
  public /*@ pure @*/ ConversionInstruction(final String a_line_text,
                                        final String a_name) {
    super(a_line_text, a_name);
  }

  /**
   * This method returns the array of conversion instructions mnemonics.
   *
   * @return the array of the handled mnemonics
   * @see InstructionLineController#getMnemonics()
   */
  public static /*@ non_null @*/ String[] getMnemonics() {
    return BytecodeStrings.CONV_INS;
  }

  /**
   * Conversion instruction line is correct if it has no parameter.
   * That means this must have the form:
   *   whitespase number : whitespace mnemonic whitespace lineend
   * where mnemonic comes from {@link BytecodeStrings#SINGLE_INS}.
   *
   * @return <code>true</code> when the instruction mnemonic is the only text
   *         in the line of the instruction text
   * @see InstructionLineController#correct()
   */
  public boolean correct() {
    return correct(BytecodeStrings.CONV_INS);
  }

  /**
   * This method, based on the value of the mnemonic
   * name, creates a new BCEL instruction
   * object for an instruction with no parameters. The method can construct
   * the following kinds of instructions:
   * <ul>
   *    <li>conversion from doubles,</li>
   *    <li>conversion from floats,</li>
   *    <li>conversion from integers,</li>
   *    <li>conversion from longs.</li>
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
    res = getD2XConvOp(res);
    res = getF2XConvOp(res);
    res = getI2XConvOp(res);
    res = getL2XConvOp(res);
    return res;
  }

  /**
   * This method creates the objects that represent instructions that convert
   * values from the long type. It checks if the name of the current instruction
   * is one of these and in that case creates an appropriate object.
   * In case the name is of a different kind it returns the parameter
   * <code>a_res</code>.
   *
   * The instructions to convert from the long type are:
   * <ul>
   *    <li>l2d,</li>
   *    <li>l2f,</li>
   *    <li>l2i.</li>
   * </ul>
   * @param a_res a helper value returned in case the current instruction is
   *   not in the current set
   * @return the object that represents the current instruction or res in
   *   case the current instruction is not in the current set
   */
  private Instruction getL2XConvOp(final Instruction a_res) {
    Instruction ires = a_res;
    if (getName().compareTo("l2d") == 0)
      ires = new L2D();
    if (getName().compareTo("l2f") == 0)
      ires = new L2F();
    if (getName().compareTo("l2i") == 0)
      ires = new L2I();
    return ires;
  }

  /**
   * This method creates the objects that represent instructions that convert
   * values from the int type. It checks if the name of the current instruction
   * is one of these and in that case creates an appropriate object.
   * In case the name is of a different kind it returns the parameter
   * <code>a_res</code>.
   *
   * The instructions to convert from the int type are:
   * <ul>
   *    <li>i2b,</li>
   *    <li>i2c,</li>
   *    <li>i2d,</li>
   *    <li>i2f,</li>
   *    <li>i2l,</li>
   *    <li>i2s.</li>
   * </ul>
   * @param a_res a helper value returned in case the current instruction is
   *   not in the current set
   * @return the object that represents the current instruction or res in
   *   case the current instruction is not in the current set
   */
  private Instruction getI2XConvOp(final Instruction a_res) {
    Instruction ires = a_res;
    if (getName().compareTo("i2b") == 0)
      ires = new I2B();
    if (getName().compareTo("i2c") == 0)
      ires = new I2C();
    if (getName().compareTo("i2d") == 0)
      ires = new I2D();
    if (getName().compareTo("i2f") == 0)
      ires = new I2F();
    if (getName().compareTo("i2l") == 0)
      ires = new I2L();
    if (getName().compareTo("i2s") == 0)
      ires = new I2S();
    return ires;
  }

  /**
   * This method creates the objects that represent instructions that convert
   * values from the float type. It checks if the name of the current
   * instruction is one of these and in that case creates an appropriate object.
   * In case the name is of a different kind it returns the parameter
   * <code>a_res</code>.
   *
   * The instructions to convert from the float type are:
   * <ul>
   *    <li>f2d,</li>
   *    <li>f2i,</li>
   *    <li>f2l.</li>
   * </ul>
   * @param a_res a helper value returned in case the current instruction is
   *   not in the current set
   * @return the object that represents the current instruction or res in
   *   case the current instruction is not in the current set
   */
  private Instruction getF2XConvOp(final Instruction a_res) {
    Instruction ires = a_res;
    if (getName().compareTo("f2d") == 0)
      ires = new F2D();
    if (getName().compareTo("f2i") == 0)
      ires = new F2I();
    if (getName().compareTo("f2l") == 0)
      ires = new F2L();
    return ires;
  }

  /**
   * This method creates the objects that represent instructions that convert
   * values from the double type. It checks if the name of the current
   * instruction is one of these and in that case creates an appropriate object.
   * In case the name is of a different kind it returns the parameter
   * <code>a_res</code>.
   *
   * The instructions to convert from the double type are:
   * <ul>
   *    <li>d2f,</li>
   *    <li>d2i,</li>
   *    <li>d2l.</li>
   * </ul>
   * @param a_res a helper value returned in case the current instruction is
   *   not in the current set
   * @return the object that represents the current instruction or res in
   *   case the current instruction is not in the current set
   */
  private Instruction getD2XConvOp(final Instruction a_res) {
    Instruction ires = a_res;
    if (getName().compareTo("d2f") == 0)
      ires = new D2F();
    if (getName().compareTo("d2i") == 0)
      ires = new D2I();
    if (getName().compareTo("d2l") == 0)
      ires = new D2L();
    return ires;
  }
}
