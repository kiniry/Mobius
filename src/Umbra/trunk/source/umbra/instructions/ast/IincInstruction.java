/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions.ast;

import org.apache.bcel.generic.IINC;
import org.apache.bcel.generic.Instruction;

import umbra.instructions.InstructionParser;
import umbra.lib.BytecodeStrings;


/**
 * This class handles the creation and correctness for iinc
 * instruction.
 *
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class IincInstruction extends NumInstruction {

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
  public IincInstruction(final String a_line_text, final String a_name) {
    super(a_line_text, a_name);
  }

  /**
   * This method returns the array of inc instructions mnemonics.
   *
   * @return the array of the handled mnemonics
   * @see InstructionLineController#getMnemonics()
   */
  public static /*@ non_null @*/ String[] getMnemonics() {
    return BytecodeStrings.IINC_INS;
  }

  /**
   * Inc instruction line is correct if it has
   * two simple number parameters (first preceded with %). The precise format
   * is as follows:
   *    whitespace number : whitespace mnemonic whitespace % number
   *    whitespace number whitespace lineend
   *
   * @return <code>true</code> when the syntax of the instruction line is
   *         correct
   * @see InstructionLineController#correct()
   */
  public final boolean correct() {
    boolean res = true;
    final InstructionParser parser = getParser();
    res = parseTillMnemonic(); //parse up to mnemonic
    res = res && (parser.swallowMnemonic(BytecodeStrings.IINC_INS) >= 0);
                           //mnemonic
    res = res && parser.swallowWhitespace(); //whitespace before the number
    res = res && parser.swallowDelimiter('%'); //
    res = res && parser.swallowNumber(); // number
    res = res && parser.swallowWhitespace();
    res = res && parser.swallowSignedNumber(); // 2nd number
    res = res && !parser.swallowWhitespace();
    return res;
  }

  /**
   * This method parses the first parameter of the current instruction.
   *
   * This method retrieves the numerical value of the parameter of the
   * instruction in {@link BytecodeLineController#getMy_line_text()}. This
   * parameter is located after the mnemonic followed by % (with no whitespace
   * inbetween). The method assumes
   * {@link BytecodeLineController#getMy_line_text()} is correct.
   *
   * @return the value of the numerical parameter of the instruction
   */
  private int getInd1() {
    final InstructionParser parser = getParser();
    parseTillMnemonic(); //parse up to mnemonic
    parser.swallowMnemonic(BytecodeStrings.IINC_INS); //mnemonic
    parser.swallowWhitespace(); //whitespace before the number
    parser.swallowDelimiter('%'); //
    parser.swallowNumber(); // number
    return parser.getResult();
  }

  /**
   * This method parses the second parameter of the current instruction.
   *
   * This method retrieves the numerical value of the parameter of the
   * instruction in {@link BytecodeLineController#getMy_line_text()}. This
   * parameter is located after the first parameter (with some whitespace
   * inbetween). The method assumes
   * {@link BytecodeLineController#getMy_line_text()} is correct. It also
   * assumes that the internal parser state has not been modified between the
   * call to {@link #getInd1()} and the call of this method.
   *
   * @return the value of the second numerical parameter of the instruction
   */
  private int getInd2() {
    final InstructionParser parser = getParser();
    parser.swallowWhitespace(); //whitespace before the number
    parser.swallowNumber(); // number
    return parser.getResult();
  }

  /**
   * This method, based on the value of the the mnemonic
   * name, creates a new BCEL instruction
   * object for the iinc instruction. It computes the parameters of the
   * instruction before the instruction is constructed.
   * This method also checks the syntactical correctness of the current
   * instruction line.
   *
   * @return the freshly constructed BCEL instruction or <code>null</code>
   *         in case the instruction is not the iinc instruction and
   *         in case the instruction line is incorrect
   * @see BytecodeLineController#getInstruction()
   */
  public final Instruction getInstruction() {

    if (!correct())
      return null;

    int index1 = 0;
    index1 = getInd1();
    int index2 = 0;
    index2 = getInd2();

    if (getName().compareTo("iinc") == 0) {
      return new IINC(index1, index2);
    }

    return null;

  }
}
