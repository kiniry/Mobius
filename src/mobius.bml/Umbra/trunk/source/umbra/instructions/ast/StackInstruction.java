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

import umbra.instructions.InstructionParser;
import umbra.lib.BytecodeStrings;


/**
 * This class handles the creation and correctness for load and store
 * instructions with parameters i.e.:
 *
 *<ul>
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
 *
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
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
   * This method returns the array of stack instructions mnemonics.
   *
   * @return the array of the handled mnemonics
   * @see InstructionLineController#getMnemonics()
   */
  public static /*@ non_null @*/ String[] getMnemonics() {
    return BytecodeStrings.STACK_INS;
  }

  /*@
    @ ensures my_line_text.contains(":") && my_line_text.contains("%");
    @*/
  /**
   * Check the correctness of a stack instruction line. The line is correct when
   * it has the form:
   *      whitespase number : whitespace mnemonic whitespace
   *      % whitespace number whitespace lineend
   *
   * @return <code>true</code> when the syntax of the instruction line is
   *         correct
   * @see InstructionLineController#correct()
   */
  public final boolean correct() {
    boolean res = true;
    final InstructionParser parser = getParser();
    res = parseTillMnemonic(); //parse up to mnemonic
    res = res && (parser.swallowMnemonic(BytecodeStrings.STACK_INS) >= 0);
                           //mnemonic
    res = res && parser.swallowWhitespace(); //whitespace before delimiter
    res = res && parser.swallowDelimiter('%'); // %
    res = res && parser.swallowWhitespace(); //whitespace before the number
    res = res && parser.swallowNumber(); // number
    res = res && !parser.swallowWhitespace();
    return res;
  }

  /*@ requires my_line_text.contains("%");
    @
    @*/
  /**
   * This method parses the parameter of the current instruction.
   *
   * This method retrieves the numerical value of the index parameter of the
   * instruction in {@link BytecodeLineController#getMy_line_text()}. This
   * parameter is located after the first '%' character in the line.
   * The method assumes {@link BytecodeLineController#getMy_line_text()}
   * is correct.
   *
   * @return the value of the numerical parameter of the instruction
   */
  protected int getInd() {
    final InstructionParser parser = getParser();
    parser.resetParser();
    parser.seekDelimiter('%'); // %
    parser.swallowWhitespace(); //whitespace before the num
    parser.swallowNumber(); // number
    return parser.getResult();
  }

  /**
   * This method, based on the value of the the mnemonic
   * name, creates a new BCEL instruction
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

    res = getAInstruction(index, res);
    res = getDInstruction(index, res);
    res = getFInstruction(index, res);
    res = getIInstruction(index, res);
    res = getLInstruction(index, res);

    return res;
  }

  /**
   * This method creates the objects that represents l-instructions. It checks
   * if the name of the current instruction is one of the l-instructions and in
   * that case creates an appropriate object. In case the name is of a different
   * kind it returns the parameter <code>a_res</code>.
   *
   * The l-instructions are:
   * <ul>
   *    <li>lload,</li>
   *    <li>lstore.</li>
   * </ul>
   *
   * @param an_index the parameter of the instruction to be created
   * @param a_res a helper value returned in case the current instruction is
   *   not an l-instruction
   * @return the object that represents the current l-instruction or res in
   *   case the current instruction is not an l-instruction
   */
  private /*@ pure @*/ Instruction getLInstruction(final int an_index,
                             final /*@ nullable @*/ Instruction a_res) {
    Instruction ires = a_res;
    if (getName().compareTo("lload") == 0) {
      ires = new LLOAD(an_index);
    }
    if (getName().compareTo("lstore") == 0) {
      ires = new LSTORE(an_index);
    }
    return ires;
  }

  /**
   * This method creates the objects that represents i-instructions. It checks
   * if the name of the current instruction is one of the i-instructions and in
   * that case creates an appropriate object. In case the name is of a different
   * kind it returns the parameter <code>a_res</code>.
   *
   * The i-instructions are:
   * <ul>
   *    <li>iload,</li>
   *    <li>istore.</li>
   * </ul>
   *
   * @param an_index the parameter of the instruction to be created
   * @param a_res a helper value returned in case the current instruction is
   *   not an i-instruction
   * @return the object that represents the current i-instruction or res in
   *   case the current instruction is not an i-instruction
   * @see BytecodeLineController#getInstruction()
   */
  private /*@ pure @*/ Instruction getIInstruction(final int an_index,
                             final /*@ nullable @*/  Instruction a_res) {
    Instruction ires = a_res;
    if (getName().compareTo("iload") == 0) {
      ires = new ILOAD(an_index);
    }
    if (getName().compareTo("istore") == 0) {
      ires = new ISTORE(an_index);
    }
    return ires;
  }

  /**
   * This method creates the objects that represents f-instructions. It checks
   * if the name of the current instruction is one of the f-instructions and in
   * that case creates an appropriate object. In case the name is of a different
   * kind it returns the parameter <code>a_res</code>.
   *
   * The f-instructions are:
   * <ul>
   *    <li>fload,</li>
   *    <li>fstore.</li>
   * </ul>
   *
   * @param an_index the parameter of the instruction to be created
   * @param a_res a helper value returned in case the current instruction is
   *   not an f-instruction
   * @return the object that represents the current f-instruction or res in
   *   case the current instruction is not an f-instruction
   */
  private /*@ pure @*/ Instruction getFInstruction(final int an_index,
                             final /*@ nullable @*/ Instruction a_res) {
    Instruction ires = a_res;
    if (getName().compareTo("fload") == 0) {
      ires = new FLOAD(an_index);
    }
    if (getName().compareTo("fstore") == 0) {
      ires = new FSTORE(an_index);
    }
    return ires;
  }

  /**
   * This method creates the objects that represents d-instructions. It checks
   * if the name of the current instruction is one of the d-instructions and in
   * that case creates an appropriate object. In case the name is of a different
   * kind it returns the parameter <code>a_res</code>.
   *
   * The d-instructions are:
   * <ul>
   *    <li>dload,</li>
   *    <li>dstore.</li>
   * </ul>
   *
   * @param an_index the parameter of the instruction to be created
   * @param a_res a helper value returned in case the current instruction is
   *   not an d-instruction
   * @return the object that represents the current d-instruction or res in
   *   case the current instruction is not a d-instruction
   */
  private /*@ pure @*/ Instruction getDInstruction(final int an_index,
                             final /*@ nullable @*/ Instruction a_res) {
    Instruction ires = a_res;
    if (getName().compareTo("dload") == 0) {
      ires = new DLOAD(an_index);
    }
    if (getName().compareTo("dstore") == 0) {
      ires = new DSTORE(an_index);
    }
    return ires;
  }

  /**
   * This method creates the objects that represents a-instructions. It checks
   * if the name of the current instruction is one of the a-instructions and in
   * that case creates an appropriate object. In case the name is of a different
   * kind it returns the parameter <code>a_res</code>.
   *
   * The a-instructions are:
   * <ul>
   *    <li>aload,</li>
   *    <li>astore.</li>
   * </ul>
   *
   * @param an_index the parameter of the instruction to be created
   * @param a_res a helper value returned in case the current instruction is
   *   not an a-instruction
   * @return the object that represents the current a-instruction or res in
   *   case the current instruction is not an a-instruction
   */
  private /*@ pure @*/ Instruction getAInstruction(final int an_index,
                             final /*@ nullable @*/ Instruction a_res) {
    Instruction ires = a_res;
    if (getName().compareTo("aload") == 0) {
      ires = new ALOAD(an_index);
    }
    if (getName().compareTo("astore") == 0) {
      ires = new ASTORE(an_index);
    }
    return ires;
  }
}
