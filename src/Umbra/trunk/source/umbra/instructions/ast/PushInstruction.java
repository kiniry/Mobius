/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions.ast;

import org.apache.bcel.generic.BIPUSH;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.SIPUSH;

import umbra.instructions.InstructionParser;
import umbra.lib.BytecodeStrings;

/**
 * This class handles the creation and correctness for push
 * instructions i.e.:
 *
 *<ul>
 *    <li>bipush,</li>
 *    <li>sipush.</li>
 * </ul>
 *
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class PushInstruction extends NumInstruction {

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
  public PushInstruction(final String a_line_text, final String a_name) {
    super(a_line_text, a_name);
  }

  /**
   * This method returns the array of push instructions mnemonics.
   *
   * @return the array of the handled mnemonics
   * @see InstructionLineController#getMnemonics()
   */
  public static /*@ non_null @*/ String[] getMnemonics() {
    return BytecodeStrings.PUSH_INS;
  }

  /**
   * Push instruction line is correct if it has one simple number parameter.
   * The exact definition of this kind of a line is as follows:
   *    whitespase number : whitespace mnemonic whitespace number
   *    whitespace lineend
   *
   * @return <code>true</code> when the syntax of the instruction line is
   *         correct
   * @see InstructionLineController#correct()
   */
  public final boolean correct() {
    boolean res = true;
    final InstructionParser parser = getParser();
    res = parseTillMnemonic(); //parse up to mnemonic
    res = res && (parser.swallowMnemonic(BytecodeStrings.PUSH_INS) >= 0);
                           //mnemonic
    res = res && parser.swallowWhitespace(); //whitespace before the number
    res = res && parser.swallowSignedNumber(); // number
    res = res && !parser.swallowWhitespace();
    return res;
  }

  /**
   * This method parses the parameter of the current instruction.
   *
   * This method retrieves the numerical value of the parameter of the
   * instruction in {@link BytecodeLineController#getMy_line_text()}. This
   * parameter is located after the mnemonic (with some whitespace inbetween).
   * The method assumes {@link BytecodeLineController#getMy_line_text()}
   * is correct.
   *
   * @return the value of the numerical parameter of the instruction
   */
  protected int getInd() {
    final InstructionParser parser = getParser();
    parser.resetParser();
    parser.seekMnemonic(BytecodeStrings.PUSH_INS); // mnemonic
    parser.swallowWhitespace(); //whitespace before the num
    parser.swallowSignedNumber(); // number
    return parser.getResult();
  }

  /**
   * This method, based on the value of the the mnemonic
   * name, creates a new BCEL instruction
   * object for a push instruction. It computes the parameter of the
   * instruction before the instruction is constructed. The method can construct
   * one of the instructions:
   * <ul>
   *    <li>bipush,</li>
   *    <li>sipush.</li>
   * </ul>
   * This method also checks the syntactical correctness of the current
   * instruction line.
   *
   * @return the freshly constructed BCEL instruction or <code>null</code>
   *         in case the instruction is not a push instruction and
   *         in case the instruction line is incorrect
   * @see BytecodeLineController#getInstruction()
   */
  public final Instruction getInstruction() {
    if (!correct())
      return null;
    final int index = getInd();
    byte b = 0;
    b = (byte)index;
    Instruction res = null;
    if (getName().compareTo("bipush") == 0) {
      res = new BIPUSH(b);
    }
    if (getName().compareTo("sipush") == 0) {
      res = new SIPUSH(b);
    }
    return res;
  }
}
