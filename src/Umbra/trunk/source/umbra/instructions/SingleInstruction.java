/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions;

import org.apache.bcel.generic.ACONST_NULL;
import org.apache.bcel.generic.ARETURN;
import org.apache.bcel.generic.ARRAYLENGTH;
import org.apache.bcel.generic.ATHROW;
import org.apache.bcel.generic.DADD;
import org.apache.bcel.generic.DDIV;
import org.apache.bcel.generic.DMUL;
import org.apache.bcel.generic.DNEG;
import org.apache.bcel.generic.DREM;
import org.apache.bcel.generic.DRETURN;
import org.apache.bcel.generic.DSUB;
import org.apache.bcel.generic.DUP;
import org.apache.bcel.generic.DUP2;
import org.apache.bcel.generic.DUP2_X1;
import org.apache.bcel.generic.DUP2_X2;
import org.apache.bcel.generic.DUP_X1;
import org.apache.bcel.generic.DUP_X2;
import org.apache.bcel.generic.FADD;
import org.apache.bcel.generic.FDIV;
import org.apache.bcel.generic.FMUL;
import org.apache.bcel.generic.FNEG;
import org.apache.bcel.generic.FREM;
import org.apache.bcel.generic.FRETURN;
import org.apache.bcel.generic.FSUB;
import org.apache.bcel.generic.IADD;
import org.apache.bcel.generic.IAND;
import org.apache.bcel.generic.IDIV;
import org.apache.bcel.generic.IMUL;
import org.apache.bcel.generic.INEG;
import org.apache.bcel.generic.IOR;
import org.apache.bcel.generic.IREM;
import org.apache.bcel.generic.IRETURN;
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
import org.apache.bcel.generic.LRETURN;
import org.apache.bcel.generic.LSHL;
import org.apache.bcel.generic.LSHR;
import org.apache.bcel.generic.LSUB;
import org.apache.bcel.generic.LUSHR;
import org.apache.bcel.generic.LXOR;
import org.apache.bcel.generic.MONITORENTER;
import org.apache.bcel.generic.MONITOREXIT;
import org.apache.bcel.generic.POP;
import org.apache.bcel.generic.POP2;
import org.apache.bcel.generic.RETURN;
import org.apache.bcel.generic.SWAP;

import umbra.UmbraHelper;
import umbra.editor.parsing.BytecodeStrings;


/**
 * This class handles the creation and correctness for certain instructions
 * with no parameters. The instructions handled here are in the following
 * categories:
 * <ul>
 *    <li>pushing the const null value on the top of the operand stack,</li>
 *    <li>arithmetic operations for doubles, floats, integers, and longs,</li>
 *    <li>array load and store instructions,</li>
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
  public SingleInstruction(final String a_line_text, final String a_name) {
    super(a_line_text, a_name);
  }

  /**
   * This method, based on the value of the field
   * {@ref InstructionLineController#my_name}, creates a new BCEL instruction
   * object for an instruction with no parameters. The method can construct
   * an instruction from one of the following families:
   * <ul>
   *    <li>pushing the const null value on the top of the operand stack,</li>
   *    <li>arithmetic operations for doubles, floats, integers, and longs,</li>
   *    <li>array load and store instructions,</li>
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
    res = getDOpInstruction(res);
    res = getFOpInstruction(res);
    res = getIOpInstruction(res);
    res = getLOpInstruction(res);
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
      final String tail = a_name.substring(a_name.indexOf('_'));
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
   * {@ref #extractConstNumber(String, int)}
   *
   * @param a_name the string with the instruction name (e.g. iload_0)
   * @return the text of the instruction name (e.g. iload for iload_0)
   */
  protected static /*@ non_null @*/ String extractInsName(
                                      final /*@ non_null @*/ String a_name) {
    return a_name.substring(0, a_name.indexOf('_'));
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
   *    <li>land,</li>
   *    <li>ldiv,</li>
   *    <li>lmul,</li>
   *    <li>lneg,</li>
   *    <li>lor,</li>
   *    <li>lrem,</li>
   *    <li>lshl,</li>
   *    <li>lshr,</li>
   *    <li>lushr,</li>
   *    <li>lxor,</li>
   *    <li>lcmp.</li>
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
    if (getName().compareTo("land") == 0)
      ires = new LAND();
    if (getName().compareTo("ldiv") == 0)
      ires = new LDIV();
    if (getName().compareTo("lmul") == 0)
      ires = new LMUL();
    if (getName().compareTo("lneg") == 0)
      ires = new LNEG();
    if (getName().compareTo("lor") == 0)
      ires = new LOR();
    if (getName().compareTo("lrem") == 0)
      ires = new LREM();
    if (getName().compareTo("lshl") == 0)
      ires = new LSHL();
    if (getName().compareTo("lshr") == 0)
      ires = new LSHR();
    if (getName().compareTo("lushr") == 0)
      ires = new LUSHR();
    if (getName().compareTo("lxor") == 0)
      ires = new LXOR();
    if (getName().compareTo("lcmp") == 0)
      ires = new LCMP();
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
   *    <li>iand,</li>
   *    <li>idiv,</li>
   *    <li>imul,</li>
   *    <li>ineg,</li>
   *    <li>ior,</li>
   *    <li>irem,</li>
   *    <li>iushr,</li>
   *    <li>ixor.</li>
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
    if (getName().compareTo("iand") == 0)
      ires = new IAND();
    if (getName().compareTo("idiv") == 0)
      ires = new IDIV();
    if (getName().compareTo("imul") == 0)
      ires = new IMUL();
    if (getName().compareTo("ineg") == 0)
      ires = new INEG();
    if (getName().compareTo("ior") == 0)
      ires = new IOR();
    if (getName().compareTo("irem") == 0)
      ires = new IREM();
    if (getName().compareTo("iushr") == 0)
      ires = new IUSHR();
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
   * Simple instruction line is correct if it has no parameter.
   *
   * @return <code>true</code> when the instruction mnemonic is the only text
   *         in the line of the instruction text
   * @see InstructionLineController#correct()
   */
  public boolean correct() {
    return correct(BytecodeStrings.SINGLE_INS);
  }

  /**
   * This method checks the correctness of the current mnemonic and if the
   * mnemonic occurs in our inventory of known mnemonics.
   *
   * @param an_inventory an array with all the correct mnemonics
   * @return <code>true</code> when the instruction mnemonic is the only text
   *         in the line of the instruction text
   * @see InstructionLineController#correct()
   */
  protected final boolean correct(final String[] an_inventory) {
    final String s = UmbraHelper.stripAllWhitespace(getMy_line_text());
    int j;
    for (j = 0; j < an_inventory.length; j++) {
      if ((s.indexOf(an_inventory[j]) > 0) &&
          (s.indexOf(an_inventory[j]) <= s.indexOf(":") + 1))
             /* s occurs in the inventory after the : which seperates the line
              * number
              */
        if (((s.indexOf(an_inventory[j])) + (an_inventory[j].length())) ==
            s.length()) // and is the only string after :
          return true;
    }
    return false;
  }
}
